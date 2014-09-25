#!/usr/bin/env sh
cp -f Make.in Make
find . -name "*.v" |grep -v misc/benchmarks_nobuild.v >>Make
coq_makefile -f Make -o Makefile