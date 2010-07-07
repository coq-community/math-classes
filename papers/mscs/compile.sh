#!/bin/sh

cp mscs.tex tmp.tex
dot -Tpdf hierarchy.dot > hierarchy.pdf

set -e
pdflatex tmp.tex
bibtex tmp
pdflatex tmp.tex
bibtex tmp
pdflatex tmp.tex
cat tmp.pdf > mscs.pdf
rm tmp.*
