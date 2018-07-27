#!/bin/sh
cp -f _CoqProject.in _CoqProject
find . -name "*.v" |grep -v misc/benchmarks_nobuild.v >> _CoqProject
