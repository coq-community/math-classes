#!/bin/sh
set -eu

dot -Tpdf hierarchy.dot > hierarchy.pdf

cp pres.tex tmp.tex
pdflatex tmp
pdflatex tmp
cp tmp.pdf pres.pdf
rm -f tmp.*
