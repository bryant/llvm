from argparse import ArgumentParser
from subprocess import Popen, PIPE
from tempfile import mktemp
import re

opts = ArgumentParser()
opts.add_argument("fn", help="function in .ll")
opts.add_argument("file", help=".ll file")
opts.add_argument("-v", "--verbose", default=False, action="store_true"),
opts.add_argument("-k", "--kuper", dest="modes", action="append_const",
                  const="kuper", help="bench kuper")
opts.add_argument("-m", "--movzx", dest="modes", action="append_const",
                  const="movzx", help="bench the movzx chompa")
opts.add_argument("-c", "--control", dest="modes", action="append_const",
                  const="control", help="bench control")
opts.add_argument("-p", "--paste", default=False, action="store_true",
                  help="bench from stdin")
opts.add_argument("-32", dest="arch", const="x86", action="store_const")
opts.add_argument("-64", dest="arch", const="amd64", action="store_const")

class FunctionNotFound(Exception): pass
class MalformedAssembly(Exception): pass
class MalformedBitcode(Exception): pass

def add_iaca_marks(asm):
    startmark = "\nud2\nmovl $111, %ebx\n.byte 0x64, 0x67, 0x90\n"
    endmark = "\nmovl $222, %ebx\n.byte 0x64, 0x67, 0x90\nud2\n"
    return startmark + asm + endmark

def extract_fn(fn, asm):
    reg = re.compile(r"^%s:.+?^\.Lfunc_end\d+:" % fn, re.M | re.DOTALL)
    rv = reg.search(asm)
    if rv is None:
        raise FunctionNotFound
    return rv.group(0)

def sanitize(asm):
    cfi_crap = re.compile(r"^\s+\.cfi.+\n", re.M)
    return cfi_crap.sub("", asm)

def llc(file, fn, extras=None):
    cmd = "llc -O3 -o -".split() + [file] + (extras or [])
    p = Popen(cmd, stdout=PIPE, stderr=PIPE)
    if p.wait() != 0:
        raise MalformedBitcode(p.stderr.read())
    rv = extract_fn(fn, p.stdout.read())
    return sanitize(rv)

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
    return gas(add_iaca_marks(sanitize(asm)), extras)

def iaca(obj, extras=None):
    cmd = ["iaca"] + (extras or ["-64"]) + [obj]
    p = Popen(cmd, stdout=PIPE)
    return p.stdout.read()

def tersify(output):
    throughput = re.compile(r"^Block Throughput:.+$", re.M)
    uops = re.compile(r"^Total Num Of Uops:.+$", re.M)
    return (throughput.search(output).group(0), uops.search(output).group(0))

MODES = {
    "kuper": "-kuper".split(),
    "movzx": "-mark-movzx -setcc-fixup".split(),
    "control": []
}

ARCHES = {
    "amd64": (
        "-march=x86-64 -mattr=+sse,+sse4.2,+avx".split(),
        [],
        ["-64"]
    ),
    "x86": (
        "-march=x86 -mattr=+sse,+sse4.2,+avx".split(),
        ["-m32"],
        ["-32"],
    )
}

def print_iaca(output, verbose=False):
    print "output", output
    if verbose:
        print output
    else:
        tp, uop = tersify(output)
        print "\t" + tp
        print "\t" + uop

def bench_plain_asm(asm, verbose=False, arch="amd64"):
    _, gccf, iacf = ARCHES[arch]
    obj = assemble(asm, gccf)
    print_iaca(iaca(obj, iacf), verbose)

def bench_bitcode_fn(file, fn, flagsets, verbose=False, arch="amd64"):
    llcf, gccf, iacf = ARCHES[arch]
    print "Testing function `%s` in file %s" % (fn, file)
    for flagset in flagsets:
        try:
            print "===", flagset, "==="
            asm = llc(file, fn, MODES[flagset] + llcf)
            obj = assemble(asm, gccf)
            print_iaca(iaca(obj, iacf), verbose)
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
    if p.paste:
        bench_plain_asm(stdin.read(), verbose=p.verbose, arch=p.arch)
    else:
        assert p.file.endswith(".ll")
        assert len(p.modes) > 0
        bench_bitcode_fn(p.file, p.fn, p.modes, arch=p.arch, verbose=p.verbose)
