#!/usr/bin/env sh
cp -f Make.in Make
find . -name "*.v" |grep -v misc/benchmarks_nobuild.v >>Make
${COQBIN}coq_makefile -f Make -o Makefile
