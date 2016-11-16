"""
Checks if FileChecks of both labels are identical.
"""

from re import sub
from itertools import ifilter, groupby, izip_longest

def collect_outputs(lines):
    mco, mssa = [], []
    check_lines = ifilter(lambda s: "; CHECK" in s or "; MCO-MSSA" in s, lines)
    for mcoty, line in groupby(check_lines, lambda s: "; CHECK" in s):
        if mcoty:
            mco.append(map(lambda s: sub("^; CHECK\S+\s+", "", s), line))
        else:
            mssa.append(map(lambda s: sub("^; MCO-MSSA\S+\s+", "", s), line))
    return mco, mssa

if __name__ == "__main__":
    from sys import stdin, argv
    from difflib import ndiff

    lines = stdin.readlines() if len(argv) < 2 else open(argv[1]).readlines()
    mco, mssa = collect_outputs(lines)
    for a, b in izip_longest(mco, mssa):
        try:
            assert a == b
        except AssertionError:
            print "Problem in", ("stdin" if len(argv) == 0 else argv[1])
            a_ = [" " * 4 + l.strip() for l in (a or [])]
            b_ = [" " * 4 + l.strip() for l in (b or [])]
            print "\n".join(ndiff(a_, b_))
            continue
