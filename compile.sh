#!/bin/sh

cp jar.tex tmp.tex
dot -Tpdf hierarchy.dot > hierarchy.pdf

set -e
pdflatex tmp.tex
bibtex tmp
pdflatex tmp.tex
bibtex tmp
pdflatex tmp.tex
cat tmp.pdf > jar.pdf
rm tmp.*
