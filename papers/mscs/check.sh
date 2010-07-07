#!/bin/sh
chktex -n 13 -n 12 -n 36 -n 26 -n 18 jar.tex
  # we suppress warnings that yield false positives for Coq code
