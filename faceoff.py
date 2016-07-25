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

class FunctionNotFound(Exception): pass

def add_iaca_marks(asm):
    startmark = "\nud2\nmovl $111, %ebx\n.byte 0x64, 0x67, 0x90\n"
    endmark = "\nmovl $222, %ebx\n.byte 0x64, 0x67, 0x90\nud2\n"
    return startmark + asm + endmark

def extract_fn(fn, asm):
    reg = re.compile(r"^%s:.+?^\.Lfunc_end\d+:" % fn, re.M | re.DOTALL)
    cfi_crap = re.compile(r"^\s+\.cfi.+\n", re.M)
    rv = reg.search(asm)
    if rv is None:
        raise FunctionNotFound
    return cfi_crap.sub("", rv.group(0))

def llc(file, fn, extras=None):
    cmd = "llc -O3 -o -".split() + [file] + (extras or [])
    return extract_fn(fn, Popen(cmd, stdout=PIPE, stderr=PIPE).stdout.read())

def assemble(asm, extras=None):
    obj = mktemp(suffix=".o")
    cmd = ("gcc -x assembler -c -o %s -" % obj).split() + (extras or [])
    p = Popen(cmd, stdin=PIPE)
    p.stdin.write(asm + "\n")
    p.stdin.close()
    p.wait()
    return obj

def iaca(asm, extras=None):
    obj = assemble(add_iaca_marks(asm))
    cmd = ["iaca"] + (extras or ["-64"]) + [obj]
    p = Popen(cmd, stdout=PIPE)
    return p.stdout.read()

MODES = {
    "kuper": "-kuper".split(),
    "movzx": "-mark-movzx -setcc-fixup".split(),
    "control": []
}

def terse(asm, extras=None):
    iaced = iaca(asm, extras)
    throughput = re.compile(r"^Block Throughput:.+$", re.M)
    uops = re.compile(r"^Total Num Of Uops:.+$", re.M)
    return (throughput.search(iaced).group(0), uops.search(iaced).group(0))

def compare_file_fn(file, fn, flagsets, verbose=False):
    print "Testing function `%s` in file %s" % (fn, file)
    for flagset in flagsets:
        print flagset
        try:
            if verbose:
                print iaca(llc(file, fn, MODES[flagset]))
            else:
                tp, uop = terse(llc(file, fn, MODES[flagset]))
                print "\t" + tp
                print "\t" + uop
        except FunctionNotFound:
            print "Function `%s` not in %s" % (fn, file)
            break

if __name__ == "__main__":
    p = opts.parse_args()
    p.modes = p.modes or ["movzx"]
    assert p.file.endswith(".ll")
    assert len(p.modes) > 0
    compare_file_fn(p.file, p.fn, p.modes, p.verbose)
