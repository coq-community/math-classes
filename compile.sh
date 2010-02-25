#!/bin/sh

lhs2TeX --agda< $1.tex > processed.tex
cp processed.tex tmp.tex

set -e
xelatex tmp.tex
bibtex tmp
xelatex tmp.tex
bibtex tmp
xelatex tmp.tex
cat tmp.pdf > $1.pdf
rm tmp.*
