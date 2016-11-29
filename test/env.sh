#!/bin/bash

alias optdbg='opt 2>&1 -debug -debug-pass=Details -print-after-all'
addpath "$(dirname $BASH_SOURCE)/../build/bin"

function clean_all {
    find ../results/ -type f -delete
}

function run_all {
    OPTFLAGS="-S -basicaa -tbaa"
    cmd="opt $OPTFLAGS -{2} {1} -o=../results/{2}/{1} 2>../results/{2}/{1}.err"
    find . -iname '*.ll' | parallel $cmd :::: - ::: memcpyopt memcpyopt-mssa
}

function lnt_benchmark {
    lntflags="--sandbox /tmp/BAR --cc clang --cxx clang++ --use-cmake=cmake \
--use-lit=llvm-lit --test-suite ~/3rd/test-suite --cmake-cache ReleaseNoLTO \
-j32"
    lnt runtest test-suite $lntflags "$@"
}
