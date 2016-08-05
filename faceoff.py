from argparse import ArgumentParser
from subprocess import Popen, PIPE
from tempfile import mktemp
from collections import namedtuple
import re

opts = ArgumentParser()
opts.add_argument("fn", help="function in .ll")
opts.add_argument("file", help=".ll file")
opts.add_argument("-v", "--verbose", default=False, action="store_true"),

opts.add_argument("-k", "--kuper", dest="modes", action="append_const",
                  const="kuper", help="bench kuper")
opts.add_argument("-m", "--movzx", dest="modes", action="append_const",
                  const="movzx", help="bench the movzx chompa")
opts.add_argument("--repair", dest="modes", action="append_const", 
                  const="repair", help="bench repair")
opts.add_argument("-c", "--control", dest="modes", action="append_const",
                  const="control", help="bench control")

opts.add_argument("-i", "--inline", default=False, action="store_true",
                  help="split stdin on semi-colons")
opts.add_argument("-32", dest="arch", const="x86", action="store_const")
opts.add_argument("-64", dest="arch", const="amd64", action="store_const")
opts.add_argument("-32n", dest="arch", const="x86n", action="store_const")
opts.add_argument("-64n", dest="arch", const="amd64n", action="store_const")
opts.add_argument("-32avx", dest="arch", const="x86avx", action="store_const")
opts.add_argument("-64avx", dest="arch", const="amd64avx", action="store_const")
opts.add_argument("-l", "--latency", default=False, action="store_true")

class FunctionNotFound(Exception): pass
class MalformedAssembly(Exception): pass
class MalformedBitcode(Exception): pass

def add_iaca_marks(asm):
    startmark = "\nud2\nmovl $111, %ebx\n.byte 0x64, 0x67, 0x90\n"
    endmark = "\nmovl $222, %ebx\n.byte 0x64, 0x67, 0x90\nud2\n"
    return startmark + asm + endmark

AsmFunc = namedtuple("AsmFunc", ("name", "body"))

def extract_fn(fn, asm):
    reg = re.compile(r"^%s:.+?^(\.Lfunc_end\d+:|\s+ret[qlb])" % fn, re.M | re.DOTALL)
    rv = reg.search(asm)
    if rv is None:
        raise FunctionNotFound
    return rv.group(0)

def extract_all_fns(asm):
    reg = re.compile(r"(^[_\$a-zA-Z0-9]+):(.+?^(?:\.Lfunc_end\d+:|\s+ret[qlb]))",
                     re.M | re.DOTALL)
    return [AsmFunc(name, body) for name, body in reg.findall(asm)]

def sanitize(asm):
    cfi_crap = re.compile(r"^\s+\..+\n", re.M)
    return cfi_crap.sub("", asm)

def llc(file, fn=None, extras=None):
    cmd = "timeout 6 llc -O3 -o -".split() + [file] + (extras or [])
    p = Popen(cmd, stdout=PIPE, stderr=PIPE)
    if p.wait() != 0:
        raise MalformedBitcode(p.stderr.read())
    rv = p.stdout.read() if fn is None else extract_fn(fn, p.stdout.read())
    return rv

def size(obj):
    p = Popen(["size", obj], stdout=PIPE, stderr=PIPE)
    p.wait()
    p.stdout.readline()
    return int(re.search(r"^\s*(\d+)", p.stdout.readline()).group(0))

def gas(asm, extras=None):
    obj = mktemp(suffix=".o")
    cmd = ("gcc -x assembler -c -o %s -" % obj).split() + (extras or [])
    p = Popen(cmd, stdin=PIPE, stderr=PIPE)
    p.stdin.write(asm + "\n")
    p.stdin.close()
    if p.wait() != 0:
        raise MalformedAssembly(p.stderr.read())
    return obj

def assemble(asm, extras=None):
    return gas(add_iaca_marks(asm), extras)

def iaca(obj, mode="throughput", extras=None):
    cmd = ["iaca"] + (extras or ["-64"]) + ["-analysis", mode.upper(), obj]
    p = Popen(cmd, stdout=PIPE)
    return p.stdout.read()

def tersify(output):
    throughput = re.compile(r"^Block Throughput:.+$", re.M)
    uops = re.compile(r"^Total Num Of Uops:.+$", re.M)
    return (throughput.search(output).group(0), uops.search(output).group(0))

def tersify_latency(output):
    latency = re.compile(r"^Latency: .+$", re.M)
    return latency.search(output).group(0)

MODES = {
    "kuper": "-kuper".split(),
    "movzx": "-setcc-fixup".split(),
    "repair": ["-zext-repair"],
    "control": []
}

ARCHES = {
    "amd64": (
        "-march=x86-64 -mattr=+sse,+sse4.2".split(),
        [],
        ["-64"]
    ),
    "x86": (
        "-march=x86 -mattr=+sse,+sse4.2".split(),
        ["-m32"],
        ["-32"],
    ),
    "amd64n": (
        "-march=x86-64 -mattr=+sse,+sse4.2,+avx".split(),
        [],
        "-64 -arch NHM".split()
    ),
    "x86n": (
        "-march=x86 -mattr=+sse,+sse4.2,+avx".split(),
        ["-m32"],
        "-32 -arch NHM".split()
    ),
    "amd64avx": (
        "-march=x86-64 -mattr=+sse,+sse4.2,+avx".split(),
        [],
        ["-64"]
    ),
    "x86avx": (
        "-march=x86 -mattr=+sse,+sse4.2,+avx".split(),
        ["-m32"],
        ["-32"],
    ),
}

def print_iaca(output, mode, verbose=False):
    if verbose:
        print output
    elif mode == "throughput":
        tp, uop = tersify(output)
        print "\t" + tp
        print "\t" + uop
    else:
        print "\t" + tersify_latency(output)

def bench_plain_asm(asm, mode, verbose=False, arch="amd64"):
    _, gccf, iacf = ARCHES[arch]
    obj = assemble(sanitize(asm), gccf)
    print_iaca(iaca(obj, mode, iacf), mode, verbose)

def bench_bitcode_fn(file, fn, flagsets, mode, verbose=False, arch="amd64"):
    llcf, gccf, iacf = ARCHES[arch]
    print "Testing function `%s` in file %s" % (fn, file)
    for flagset in flagsets:
        try:
            print "===", flagset, "==="
            asm = llc(file, fn, MODES[flagset] + llcf)
            obj = assemble(sanitize(asm), gccf)
            print_iaca(iaca(obj, mode, iacf), mode, verbose)
        except FunctionNotFound:
            print "Function `%s` not in %s" % (fn, file)
            break
        except MalformedAssembly as e:
            print "Assembler fail:", e
            break
        except MalformedBitcode as e:
            print "llc fail:", e
            break

if __name__ == "__main__":
    from sys import stdin
    p = opts.parse_args()
    p.modes = p.modes or ["movzx"]
    p.arch = p.arch or "amd64"
    m = "latency" if p.latency else "throughput"
    if p.file == "-":
        asm = stdin.read().replace(";", "\n") if p.inline else stdin.read()
        bench_plain_asm(asm, m, verbose=p.verbose, arch=p.arch)
    else:
        assert p.file.endswith(".ll")
        assert len(p.modes) > 0
        bench_bitcode_fn(p.file, p.fn, p.modes, m, arch=p.arch,
                         verbose=p.verbose)
