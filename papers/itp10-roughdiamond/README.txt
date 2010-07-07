We use lhs2TeX [1] for the preparation of our paper. lhs2TeX is a preprocessor which takes 
almost-TeX as input and produces TeX as output.

See compile.sh for how we invoke lhs2TeX and pdflatex.

As you can see, processed.tex is the result of running lhs2TeX on our hand-crafted almost-TeX 
(paper.tex). It, together with
  - abstract.ltx
  - macros.sty
  - paper.bib
  - llncs.cls
  - splncs.bst
, are compiled by pdflatex to produce the final pdf (paper.pdf).

We provide paper.tex so that, should there be a problem with processed.tex, the latter can be 
regenerated from paper.tex using lhs2TeX.

The version of lhs2TeX we used is 1.13, but it should not matter, because processed.tex should 
not depend on lhs2TeX in any way.

[1] http://people.cs.uu.nl/andres/lhs2tex/
