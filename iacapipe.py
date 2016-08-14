from faceoff import read_elf_fns, objcopy, objdump, add_iaca_bytes, iaca, arch_type
from argparse import ArgumentParser
from sys import stdin, stderr
from tempfile import mktemp
import re

opts = ArgumentParser()
opts.add_argument("obj", help="object file")
#opts.add_argument("mode", help="kuper, movzx, control")
#opts.add_argument("arch", help=", ".join(ARCHES.iterkeys()))

def summarize(raw, extras=None):
    fnbin = mktemp(suffix=".bin")
    with open(fnbin, "w") as f:
        f.write(add_iaca_bytes(raw))
    thr = iaca(fnbin, extras=extras)
    lat = iaca(fnbin, mode="latency", extras=extras)
    return "; ".join([
        re.search(r"^Block (Throughput:.+?) Cycles", thr, re.M).group(1),
        re.search(r"^Total Num Of (Uops:.+$)", thr, re.M).group(1),
        re.search(r"^(Latency: .+) Cycles", lat, re.M).group(1),
        "Size: %d" % len(raw)
    ])

p = opts.parse_args()
#m = MODES[p.mode]
bin = open(objcopy(p.obj)).read()
iacf = "-32" if arch_type(p.obj) == "x86" else "-64"
for fn, start, end in read_elf_fns(p.obj):
    summary = summarize(bin[start:end], extras=[iacf])
    body = objdump(p.obj, range_=(start, end))
    print "#", summary
    print fn + ":"
    print body
