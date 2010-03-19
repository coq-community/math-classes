#!/bin/sh

lhs2TeX --agda< $1.tex > processed.tex
cp processed.tex tmp.tex

set -e
pdflatex tmp.tex
bibtex tmp
pdflatex tmp.tex
bibtex tmp
pdflatex tmp.tex
cat tmp.pdf > $1.pdf
rm tmp.*
