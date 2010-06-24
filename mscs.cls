%%
%% This is file `mscs.cls'
%%
%% CUP Journal MSCS document class
%% Copyright (1996-2001) Cambridge University Press
%%
%% by Mark A. Reed
%%   based on MSCS.STY
%%
%% Bugs (in the case of unchanged files) should be reported to
%% texline@cambridge.org
%%
%% This software may only be used in the preparation of journal articles
%% or books or parts of books to be published by Cambridge University Press.
%% Any other use constitutes an infringement of copyright.
%%
%% \CharacterTable
%%  {Upper-case    \A\B\C\D\E\F\G\H\I\J\K\L\M\N\O\P\Q\R\S\T\U\V\W\X\Y\Z
%%   Lower-case    \a\b\c\d\e\f\g\h\i\j\k\l\m\n\o\p\q\r\s\t\u\v\w\x\y\z
%%   Digits        \0\1\2\3\4\5\6\7\8\9
%%   Exclamation   \!     Double quote  \"     Hash (number) \#
%%   Dollar        \$     Percent       \%     Ampersand     \&
%%   Acute accent  \'     Left paren    \(     Right paren   \)
%%   Asterisk      \*     Plus          \+     Comma         \,
%%   Minus         \-     Point         \.     Solidus       \/
%%   Colon         \:     Semicolon     \;     Less than     \<
%%   Equals        \=     Greater than  \>     Question mark \?
%%   Commercial at \@     Left bracket  \[     Backslash     \\
%%   Right bracket \]     Circumflex    \^     Underscore    \_
%%   Grave accent  \`     Left brace    \{     Vertical bar  \|
%%   Right brace   \}     Tilde         \~}
%%

\NeedsTeXFormat{LaTeX2e}[1997/12/01]
\ProvidesClass{mscs}[2001/10/03 v1.27 Mathematical Structures in Computer
  ^^JScience document class]

\newif\ifprodtf

\DeclareOption{oneside}{\relax}
\DeclareOption{twoside}{\@twosidetrue \@mparswitchtrue}
\DeclareOption{draft}{\setlength\overfullrule{5\p@}}
\DeclareOption{final}{\setlength\overfullrule{\z@}}
\DeclareOption{onecolumn}{\@twocolumnfalse}
\DeclareOption{twocolumn}{\relax}
\DeclareOption{titlepage}{\relax}
\DeclareOption{notitlepage}{\relax}
\DeclareOption{leqno}{\relax}
\DeclareOption{fleqn}{\relax}
\DeclareOption{prodtf}{\prodtftrue}

\ExecuteOptions{twoside,final,onecolumn}
\ProcessOptions\relax

\ifprodtf \RequirePackage{CUPTimes,mscs2esy}\fi

\setlength\lineskip{1\p@}
\setlength\normallineskip{1\p@}
\renewcommand\baselinestretch{}

\renewcommand\normalsize{%
  \@setfontsize\normalsize\@xpt{13}%
  \abovedisplayskip 6.5\p@ \@plus 1\p@ \@minus 1\p@
  \belowdisplayskip \abovedisplayskip
  \abovedisplayshortskip 3\p@ \@plus 1\p@
  \belowdisplayshortskip \abovedisplayshortskip
  \let\@listi\@listI
}

\normalsize

\newdimen\oneem \oneem=1em

\newcommand\small{%
  \@setfontsize\small\@ixpt{12}%
  \abovedisplayskip 6\p@ \@plus 1\p@ \@minus 1\p@
  \belowdisplayskip \abovedisplayskip
  \abovedisplayshortskip 3\p@ \@plus 1\p@
  \belowdisplayshortskip \abovedisplayshortskip
  \def\@listi{\leftmargin\leftmargini
    \topsep 2\p@ \@plus 1\p@ \@minus 1\p@
    \parsep \z@
    \itemsep \parsep}%
}

\newcommand\footnotesize{%
  \@setfontsize\footnotesize\@viiipt{10}%
  \abovedisplayskip 5\p@ \@plus 1\p@ \@minus 1\p@
  \belowdisplayskip \abovedisplayskip
  \abovedisplayshortskip \z@ \@plus 1\p@
  \belowdisplayshortskip \abovedisplayshortskip
  \def\@listi{\leftmargin\leftmargini
    \topsep 2\p@ \@plus 1\p@ \@minus 1\p@
    \parsep \z@
    \itemsep \parsep}%
}

\newcommand\indexsize{\@setfontsize\indexsize\@viiipt{9}}
\newcommand\scriptsize{\@setfontsize\scriptsize\@viipt{8}}
\newcommand\tiny{\@setfontsize\tiny\@vpt{6}}
\newcommand\large{\@setfontsize\large\@xiipt{14}}
\newcommand\Large{\@setfontsize\Large\@xivpt{18}}
\newcommand\LARGE{\@setfontsize\LARGE\@xviipt{21}}
\newcommand\huge{\@setfontsize\huge\@xxpt{25}}
\newcommand\Huge{\@setfontsize\Huge\@xxvpt{30}}

\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
\DeclareRobustCommand*{\cal}{\@fontswitch{\relax}{\mathcal}}
\DeclareRobustCommand*{\mit}{\@fontswitch{\relax}{\mathnormal}}

\ifprodtf \else
  \setlength\oddsidemargin{2pc}
  \setlength\evensidemargin{2pc}
  \setlength\topmargin{3pc}
\fi

\setlength\marginparwidth{2.0cm}
\setlength\marginparsep{10\p@}

\setlength\headheight{13\p@}
\setlength\headsep{13\p@}
\setlength\topskip{13\p@}
\setlength\footskip{26\p@}

\setlength\textheight{43\baselineskip}
\addtolength\textheight{\topskip}
\setlength\textwidth{32pc}
\setlength\columnsep{10\p@}
\setlength\columnseprule{\z@}

\setlength\footnotesep{6.65\p@}
\setlength{\skip\footins}{19.5\p@ \@plus 12\p@ \@minus 1\p@}

\setlength\floatsep{13\p@ \@plus 6.5\p@ \@minus 1\p@}
\setlength\textfloatsep{15\p@ \@plus 4.5\p@ \@minus 3\p@}
\setlength\intextsep{13\p@ \@plus 6.5\p@ \@minus 2\p@}

\setlength\dblfloatsep{13\p@ \@plus 6.5\p@ \@minus 2\p@}
\setlength\dbltextfloatsep{15\p@ \@plus 4.5\p@ \@minus 3\p@}
\setlength\@fptop{\z@ \@plus 0fil}
\setlength\@fpsep{13\p@ \@plus 0fil}
\setlength\@fpbot{\z@ \@plus 3fil}
\setlength\@dblfptop{\z@ \@plus 0fil}
\setlength\@dblfpsep{13\p@ \@plus 0fil}
\setlength\@dblfpbot{\z@ \@plus 3fil}
\setlength\marginparpush{5\p@}

\setlength\parskip{\z@ \@plus .3\p@}
\setlength\parindent{1em}
\setlength\partopsep{\z@ \@plus 1\p@}
\@lowpenalty  51
\@medpenalty 151
\@highpenalty 301
\@beginparpenalty -\@lowpenalty
\@endparpenalty -\@lowpenalty
\@itempenalty -\@lowpenalty
\clubpenalty\z@
\widowpenalty\@M

\newcommand\section{%
  \@startsection{section}{1}{\z@}
    {-19.5\p@ \@plus -6.5\p@ \@minus -3.25\p@}
    {6.5\p@ \@minus 1\p@}
    {\normalsize\normalfont\bfseries\raggedright}%
}

\newcommand\subsection{%
  \@startsection{subsection}{2}{\z@}
    {-19.5\p@ \@plus -3.25\p@ \@minus -3.25\p@}
    {6.5\p@ \@minus 1\p@}
    {\normalsize\normalfont\itshape\raggedright}%
}

\newcommand\subsubsection{%
  \@startsection{subsubsection}{3}{\z@}
    {13\p@ \@plus 3.25\p@ \@minus 1\p@}
    {-0.5em}
    {\normalsize\normalfont\itshape}%
}

\newcommand\paragraph{%
  \@startsection{paragraph}{4}{\z@}
    {13\p@ \@plus 3.25\p@ \@minus 1\p@}
    {-0.5em}
    {\normalsize\normalfont\rmfamily}%
}

\newcommand\subparagraph{%
  \@startsection{subparagraph}{4}{\parindent}
    {13\p@ \@plus 3.25\p@ \@minus 1\p@}
    {-0.5em}
    {\normalsize\normalfont\rmfamily}%
}

\newcommand\xhead{% as \section
  \@startsection{section}{5}{\z@}
    {-19.5\p@ \@plus -6.5\p@ \@minus -3.25\p@}
    {6.5\p@ \@minus 1\p@}
    {\normalsize\normalfont\bfseries\raggedright}%
}

\newif\ifappendix \appendixfalse

\def\@startsection#1#2#3#4#5#6{% FROM LATEX.LTX
  \if@noskipsec \leavevmode \fi
  \par \@tempskipa #4\relax
  \@afterindenttrue
  \ifdim \@tempskipa <\z@
    \@tempskipa -\@tempskipa \@afterindentfalse
  \fi
  \if@nobreak
    \everypar{}%
  \else
    \addpenalty{\@secpenalty}\addvspace{\@tempskipa}%
  \fi
  \@ifstar
  {\@ssect{#3\ifappendix\ifnum #2=\@ne \appendixname. %
    \addcontentsline{toc}{#1}{\appendixname}\fi\fi}{#4}{#5}{#6}}%
  {\@dblarg{\@sect{#1}{#2}{#3}{#4}{#5}{#6}}}%
}

\def\rm@seccntformat#1{{\normalfont\rmfamily\csname the#1\endcsname.\enskip}}
\def\bf@seccntformat#1{{\normalfont\bfseries\ifappendix \appendixname\ \fi
  \csname the#1\endcsname.\enskip}}

\def\numberline#1{\hb@xt@\@tempdima{#1\hss}}

\def\@sect#1#2#3#4#5#6[#7]#8{% FROM LATEX.LTX
  \ifnum #2>\c@secnumdepth
    \let\@svsec\@empty
  \else
    \refstepcounter{#1}%
    \ifnum #2>\@ne
      \protected@edef\@svsec{\rm@seccntformat{#1}}%
    \else
      \protected@edef\@svsec{\bf@seccntformat{#1}}%
    \fi
  \fi
  \@tempskipa #5\relax
  \ifdim \@tempskipa>\z@
    \begingroup #6\relax
    \@hangfrom{\hskip #3\relax\@svsec}%
    {\interlinepenalty \@M #8\par}%
    \endgroup
    \csname #1mark\endcsname{#7}%
    \addcontentsline{toc}{#1}{%
      \ifnum #2>\c@secnumdepth
      \else
        \protect\numberline{\ifnum#2=\@ne\ifappendix \appendixname\ \fi\fi
          \csname the#1\endcsname}%
      \fi
      \ifnum#2=\@ne\ifappendix \hspace{48\p@}\fi\fi
    #7}%
  \else
    \def\@svsechd{#6\hskip #3\relax
      \@svsec #8\csname #1mark\endcsname{#7}%
      \addcontentsline{toc}{#1}{%
        \ifnum #2>\c@secnumdepth
        \else
          \protect\numberline{\csname the#1\endcsname}%
        \fi
      #7}%
    }%
  \fi
  \@xsect{#5}%
}

\newcommand\appendix{\par
  \appendixtrue
  \setcounter{section}\z@
  \setcounter{subsection}\z@
  \def\thesection{\@Alph\c@section}%
  \def\thesubsection{\thesection.\@arabic\c@subsection}%
  \def\thesubsubsection{\thesubsection.\@arabic\c@subsubsection}%
}

\setlength\leftmargini   {1.25pc}
\setlength\leftmarginii  {1.25pc}
\setlength\leftmarginiii {1.25pc}
\setlength\leftmarginiv  {1.25pc}
\setlength\leftmarginv   {1pc}
\setlength\leftmarginvi  {1pc}

\setlength\leftmargin   {\leftmargini}
\setlength\labelsep     {2.5\p@}
\setlength\labelwidth   {\leftmargini}
\addtolength\labelwidth {-\labelsep}

\def\makeRLlabel#1{\rlap{#1}\hss}
\def\makeRRlabel#1{\hss\llap{#1}}

\def\@listI{%
  \leftmargin\leftmargini
  \parsep \z@
  \topsep 3\p@ \@plus 1\p@ \@minus 1\p@
  \itemsep \z@ \@plus 1\p@ \@minus 1\p@
}
\let\@listi\@listI
\@listi

\def\@listii{%
  \leftmargin\leftmarginii
  \labelwidth\leftmarginii
  \advance\labelwidth-\labelsep
  \topsep 3\p@ \@plus 1\p@ \@minus 1\p@
  \parsep \z@
  \itemsep \parsep
}

\def\@listiii{%
  \leftmargin\leftmarginiii
  \labelwidth\leftmarginiii
  \advance\labelwidth-\labelsep
  \topsep 3\p@ \@plus 1\p@ \@minus 1\p@
  \parsep \z@
  \partopsep \z@
  \itemsep \topsep
}

\def\@listiv{%
  \leftmargin\leftmarginiv
  \labelwidth\leftmarginiv
  \advance\labelwidth-\labelsep
}

\def\@listv{%
  \leftmargin\leftmarginv
  \labelwidth\leftmarginv
  \advance\labelwidth-\labelsep
}

\def\@listvi{%
  \leftmargin\leftmarginvi
  \labelwidth\leftmarginvi
  \advance\labelwidth-\labelsep
}

\renewenvironment{itemize}
  {\ifnum \@itemdepth>\thr@@
     \@toodeep
   \else
     \advance\@itemdepth \@ne
     \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
     \list{\csname\@itemitem\endcsname}%
       {\let\makelabel\makeRLlabel}%
   \fi}
  {\endlist}

\newcommand\labelitemi{\normalfont\bfseries ---}
\newcommand\labelitemii{\normalfont\bfseries --}
\newcommand\labelitemiii{$\m@th\bullet$}
\newcommand\labelitemiv{$\m@th\cdot$}

\renewenvironment{enumerate}
  {\ifnum \@enumdepth>\thr@@
     \@toodeep
   \else
     \advance\@enumdepth \@ne
     \edef\@enumctr{enum\romannumeral\the\@enumdepth}%
   \fi
   \@ifnextchar [{\@enumeratetwo}{\@enumerateone}}
  {\endlist}

\def\@enumeratetwo[#1]{%
  \list{\csname label\@enumctr\endcsname}%
   {\settowidth\labelwidth{#1}%
    \leftmargin\labelwidth
    \advance\leftmargin\labelsep
    \usecounter{\@enumctr}%
   \let\makelabel\makeRLlabel}%
}

\def\@enumerateone{%
  \list{\csname label\@enumctr\endcsname}%
   {\usecounter{\@enumctr}%
   \let\makelabel\makeRLlabel}%
}

\newcommand\labelenumi  {\theenumi}
\renewcommand\theenumi  {\@arabic\c@enumi}
\newcommand\labelenumii {(\theenumii)}
\renewcommand\theenumii {\@alph\c@enumii}
\renewcommand\p@enumii  {\theenumi}
\newcommand\labelenumiii{\theenumiii}
\renewcommand\theenumiii{\@roman\c@enumiii}
\renewcommand\p@enumiii {\theenumi(\theenumii)}
\newcommand\labelenumiv {\theenumiv}
\renewcommand\theenumiv {\@Alph\c@enumiv}
\renewcommand\p@enumiv  {\p@enumiii\theenumiii}

\newcommand*\descriptionlabel[1]{\hspace\labelsep \normalfont\bfseries #1}
\newenvironment{description}
  {\list{}{\labelwidth\z@
           \itemindent-\leftmargin
   \let\makelabel\descriptionlabel}}
  {\endlist}

\newenvironment{verse}
  {\let\\=\@centercr
   \list{}{\itemsep\z@
     \itemindent -1.25pc
     \listparindent \itemindent
     \rightmargin\leftmargin
     \advance\leftmargin 1.25pc}\item[]}
  {\endlist}

\newenvironment{quotation}
  {\list{}{\listparindent 1em%
    \itemindent\listparindent
    \leftmargin\z@
    \rightmargin\leftmargin
    \parsep \z@ \@plus 1\p@}\item[]%
    \small\normalfont}
  {\endlist}

\newenvironment{quote}
  {\quotation}
  {\endquotation}

\newcommand\maketitle{\par
  \begingroup
    \def\@makefnmark{{$^{\@thefnmark}$}}%
    \newpage
    \global\@topnum\z@
    \@maketitle \thispagestyle{titlepage}\@thanks
  \endgroup
  \setcounter{footnote}\z@
  \global\let\@maketitle\relax
  \global\let\@thanks\relax
  \global\let\@title\relax
  \global\let\@author\relax
  \global\let\maketitle\relax
  \global\let\thanks\relax
}

\renewcommand\and{%
  \end{author@tabular}\vskip 6\p@\par
  \begin{author@tabular}[t]{@{}l@{}}%
}

\let\addressbreak\relax

\def\author@tabular{\def\@halignto{}\@authortable}
\let\endauthor@tabular=\endtabular
\def\author@tabularcr{{\ifnum0=`}\fi
  \@xtabularcr[5\p@]\small\normalfont\itshape\ignorespaces}
\def\author@tabularcrnospace{{\ifnum0=`}\fi
  \@xtabularcr[-2\p@]\small\normalfont\itshape\ignorespaces}
\def\@authortable{\leavevmode \hbox \bgroup $\let\@acol\@tabacol
 \let\@classz\@tabclassz \let\@classiv\@tabclassiv
 \let\\\author@tabularcr \@tabarray}

\def\@maketitle{%
  \newpage
  \vspace*{3\p@}%
  {\raggedright \sloppy
  {\LARGE\strut \normalfont\bfseries \@title \par}%
  \vskip 14\p@
  {\normalsize\normalfont
   \let\addressbreak\author@tabularcrnospace
   \begin{author@tabular}[t]{@{}l@{}}\@author
   \end{author@tabular}\par}%
  \vskip 13\p@
  {\small\strut\normalfont\itshape Received \@date}}%
  \par\noindent
  \vskip 37\p@
}

\newenvironment{abstract}
  {\list{}{\leftmargin\z@
    \rightmargin 2pc
    \parsep \z@ \@plus 1\p@}%
   \raggedright\item[]\small\normalfont}
  {\endlist}

\mark{{}{}}
\gdef\@author{\mbox{}}
\renewcommand\author{\@ifnextchar [{\@authortwo}{\@authorone}}
\def\@authortwo[#1]#2{\gdef\@author{#2}\gdef\@shortauthor{#1}}
\def\@authorone#1{\gdef\@author{#1}\gdef\@shortauthor{#1}}
\newcommand\shortauthor[1]{\gdef\@shortauthor{#1}}
\gdef\@shortauthor{}
\gdef\@title{\mbox{}}
\renewcommand\title{\@ifnextchar [{\@titletwo}{\@titleone}}
\def\@titletwo[#1]#2{\gdef\@title{#2}\gdef\@shorttitle{#1}}
\def\@titleone#1{\gdef\@title{#1}\gdef\@shorttitle{#1}}
\newcommand\shorttitle[1]{\gdef\@shorttitle{#1}}
\gdef\@shorttitle{}
\newcommand\pubyear[1]{\gdef\@year{#1}}
\gdef\@year{19XX}
\newcommand\volume[1]{\gdef\@volume{#1}}
\gdef\@volume{00}
\newcommand\pagerange[1]{\gdef\@pagerange{#1}}
\gdef\@pagerange{1--000}
\def\press{DOI: \@doi\quad {Printed in the United Kingdom}}
\newcommand\doi[1]{\gdef\@doi{10.1017/#1}}
\gdef\@doi{10.1017/S0000000000000000}

\newcommand\journal[1]{\gdef\@journal{#1}}
\def\@journal{%
  \vbox to 5.6\p@{\noindent
    \parbox[t]{5in}{%
      \ifprodtf
        {\normalfont\itshape Math. Struct. in Comp. Science\/}
        (\@year), {\normalfont\itshape vol.} \@volume, {\normalfont\itshape pp.}
        \@pagerange.\quad \copyright\ \@year\ Cambridge University 
        Press\\[2.5\p@]
       \press
      \else
        {\normalfont\itshape Under consideration for publication in
         Math. Struct. in Comp. Science}%
      \fi}%
  \vss}%
}

\def\ps@headings{\let\@mkboth\markboth
  \def\@oddhead{\normalfont\rmfamily {\itshape\@shorttitle}\hfill \thepage}%
  \def\@evenhead{\normalfont\rmfamily {\itshape\@shortauthor}\hfill \thepage}%
  \let\@evenfoot\@empty
  \let\@oddfoot\@evenfoot
  \def\sectionmark##1{\markboth{##1}{}}%
  \def\subsectionmark##1{\markright{##1}}%
}

\def\ps@myheadings{\let\@mkboth\@gobbletwo
  \def\@oddhead{\normalfont\rmfamily {\itshape\rightmark}\hfill \thepage}%
  \def\@evenhead{\normalfont\rmfamily {\itshape\leftmark}\hfill \thepage}%
  \let\@oddfoot\@empty
  \let\@evenfoot\@oddfoot
  \let\sectionmark\@gobble
  \let\subsectionmark\@gobble
}

\def\ps@titlepage{\leftskip\z@ \let\@mkboth\@gobbletwo
  \def\@oddhead{\footnotesize\normalfont\@journal \hfill}%
  \def\@evenhead{\footnotesize\normalfont\@journal \hfill}%
  \let\@oddfoot\@empty
  \let\@evenfoot\@oddfoot
  \let\sectionmark\@gobble
  \let\subsectionmark\@gobble
}

\def\@xnthm#1#2[#3]{% FROM LATEX.LTX
\expandafter\@ifdefinable\csname #1\endcsname
  {\@definecounter{#1}\@newctr{#1}[#3]%
   \expandafter\xdef\csname the#1\endcsname{\expandafter\noexpand
   \csname the#3\endcsname \@thmcountersep \@thmcounter{#1}}%
   \global\@namedef{#1}{\@thm{#1}{#2}}%
   \global\@namedef{#1*}{\@thmstar{#1}{#2}}%
   \global\@namedef{end#1}{\@endtheorem}%
   \global\@namedef{end#1*}{\@endthmstar}}%
}

\def\@ynthm#1#2{% FROM LATEX.LTX
\expandafter\@ifdefinable\csname #1\endcsname
  {\@definecounter{#1}%
   \expandafter\xdef\csname the#1\endcsname{\@thmcounter{#1}}%
   \global\@namedef{#1}{\@thm{#1}{#2}}%
   \global\@namedef{#1*}{\@thmstar{#1}{#2}}%
   \global\@namedef{end#1}{\@endtheorem}%
   \global\@namedef{end#1*}{\@endthmstar}}%
}

\def\@othm#1[#2]#3{% FROM LATEX.LTX
  \@ifundefined{c@#2}{\@nocounterr{#2}}%
    {\expandafter\@ifdefinable\csname #1\endcsname
    {\global\@namedef{the#1}{\@nameuse{the#2}}%
     \global\@namedef{#1}{\@thm{#2}{#3}}%
     \global\@namedef{#1*}{\@thmstar{#2}{#3}}%
     \global\@namedef{end#1}{\@endtheorem}%
     \global\@namedef{end#1*}{\@endthmstar}}}%
}

\def\@thmstar#1#2{\@ifnextchar[{\@ythmstar{#1}{#2}}{\@xthmstar{#1}{#2}}}
\def\@xthmstar#1#2{\@beginthmstar{#2}{\csname the#1\endcsname}\ignorespaces}
\def\@ythmstar#1#2[#3]{\@opargbeginthmstar{#2}{\csname the#1\endcsname}{#3}%
  \ignorespaces}

\def\@thmstarcounter#1{{}}
\def\@thmstarcountersep{{}}

\newif\ifrembrks
\newcommand\removebrackets{\rembrkstrue}

\def\thm@body{\topsep .5\baselineskip \@plus .2\baselineskip
  \leftmargin\z@ \rightmargin\leftmargin \listparindent\parindent
}

\def\prf@body{\thm@body \itemindent\parindent \labelsep\z@ \labelwidth\z@}

\def\@begintheorem#1#2{\list{}{\thm@body}%
  \item[]{\normalfont\bfseries #1\ #2.}%
  \normalfont\rmfamily\enskip\ignorespaces}

\def\@opargbegintheorem#1#2#3{\list{}{\thm@body}%
  \item[]{\normalfont\bfseries #1\ #2\ %
          \ifrembrks #3\global\rembrksfalse\else (#3)\fi.}%
  \normalfont\rmfamily\enskip\ignorespaces}

\let\@endtheorem\endlist

\def\@beginthmstar#1#2{\list{}{\thm@body}%
  \item[]{\normalfont\bfseries #1.}%
  \normalfont\rmfamily\enskip\ignorespaces}

\def\@opargbeginthmstar#1#2#3{\list{}{\thm@body}%
  \item[]{\normalfont\bfseries #1\ %
          \ifrembrks #3\global\rembrksfalse\else (#3)\fi.}%
  \normalfont\rmfamily\enskip\ignorespaces}

\let\@endthmstar\endlist

\newsavebox{\proofbox}
\savebox{\proofbox}{%
  \begin{picture}(7,7)\put(0,0){\framebox(7,7){}}\end{picture}%
}

\newenvironment{proof}
  {\@ifnextchar[{\@oprf}{\@nprf}}
  {\hspace*{\fill}{\usebox{\proofbox}}\endlist}

\newenvironment{proof*}{\proof}{\endlist}

\def\@oprf[#1]{%
  \list{}{\prf@body}%
  \item[]{{\normalfont\itshape #1}}%
  \normalfont\rmfamily\enskip\ignorespaces
}

\def\@nprf{%
  \list{}{\prf@body}%
  \item[]{\normalfont\itshape Proof.}%
  \normalfont\rmfamily\enskip\ignorespaces
}

\setlength\arraycolsep       {5\p@}
\setlength\tabcolsep         {6\p@}
\setlength\arrayrulewidth    {.5\p@}
\setlength\doublerulesep     {1.5\p@}

\setlength\tabbingsep        {\labelsep}
\setlength{\skip\@mpfootins} {10\p@ \@plus 5\p@ \@minus 1\p@}

\setlength\fboxsep           {3\p@}
\setlength\fboxrule          {.5\p@}

\setcounter{secnumdepth}{3}
\newcounter{part}
\newcounter{section}
\newcounter{subsection}[section]
\newcounter{subsubsection}[subsection]
\newcounter{paragraph}[subsubsection]
\newcounter{subparagraph}[paragraph]
\renewcommand\thepart          {\@arabic\c@part}
\renewcommand\thesection       {\@arabic\c@section}
\renewcommand\thesubsection    {\thesection.\@arabic\c@subsection}
\renewcommand\thesubsubsection {\thesubsection.\@arabic\c@subsubsection}
\renewcommand\theparagraph     {\thesubsubsection.\@arabic\c@paragraph}
\renewcommand\thesubparagraph  {\theparagraph.\@arabic\c@subparagraph}

\def\@pnumwidth{1.55em}
\def\@tocrmarg {2.55em}
\def\@dotsep{4.5}
\setcounter{tocdepth}{2}

\def\@dottedtocline#1#2#3#4#5{% FROM LATEX.LTX
  \ifnum #1>\c@tocdepth \else
    \vskip \z@ \@plus.2\p@
    {\leftskip #2\relax
     \rightskip\@tocrmarg \parfillskip -\rightskip
     \parindent #2\relax\@afterindenttrue
     \interlinepenalty\@M
     \leavevmode
     \@tempdima #3\relax
     \advance\leftskip \@tempdima \null\nobreak\hskip -\leftskip
     {#4}\nobreak
%     \leaders\hbox{$\m@th
%        \mkern \@dotsep mu\hbox{.}\mkern \@dotsep
%        mu$}%
     \hfill\nobreak
     \hb@xt@\@pnumwidth{\hfil\normalfont \normalcolor #5}%
     \par}%
  \fi}

\newcommand\tableofcontents{%
  \xhead*{\contentsname}\@starttoc{toc}%
  \par\vspace{13\p@}%
}

\newcommand*\l@section[2]{\addpenalty{\@secpenalty}%
 \@tempdima 1.5em%
 \begingroup
  \parindent \z@ \rightskip \@pnumwidth
  \parfillskip -\@pnumwidth \normalfont\rmfamily \leavevmode
  \advance\leftskip\@tempdima \hskip -\leftskip
  #1\nobreak\hfil \nobreak\hb@xt@\@pnumwidth{\hss #2}\par
 \endgroup}

\newcommand*\l@subsection{\@dottedtocline{2}{1.5em}{2.3em}}
\newcommand*\l@subsubsection{\@dottedtocline{3}{3.8em}{3.2em}}
\newcommand*\l@paragraph{\@dottedtocline{4}{7.0em}{4.1em}}
\newcommand*\l@subparagraph{\@dottedtocline{5}{10em}{5em}}

\newcommand\listoffigures{%
  \xhead*{\listfigurename}\@starttoc{lof}%
}

\newcommand*\l@figure{\@dottedtocline{1}{1.5em}{2.3em}}
\let\l@table\l@figure

\newcommand\listoftables{%
  \xhead*{\listtablename}\@starttoc{lot}%
}

\newenvironment{thebibliography}[1]
  {\xhead*{\refname}%
   \addcontentsline{toc}{section}{\refname}%
   \list{}{\labelwidth\z@ \leftmargin 1em \itemindent-\leftmargin}%
   \small\normalfont \parindent\z@
   \parskip\z@ \@plus .1\p@\relax
   \sloppy\clubpenalty\z@ \widowpenalty\@M
   \sfcode`\.\@m\relax}
  {\def\@noitemerr
       {\@latex@warning{Empty `thebibliography' environment}}%
   \endlist}

\newcommand\newblock{\hskip .11em\@plus.33em\@minus.07em}

\def\@cite#1#2{(#1\if@tempswa , #2\fi)}% FROM LATEX.LTX
\def\@biblabel#1{}% FROM LATEX.LTX

\def\@citex[#1]#2{% FROM LATEX.LTX
  \let\@citea\@empty
  \@cite{\@for\@citeb:=#2\do
    {\@citea\def\@citea{;\ }%
     \edef\@citeb{\expandafter\@firstofone\@citeb\@empty}%
     \if@filesw\immediate\write\@auxout{\string\citation{\@citeb}}\fi
     \@ifundefined{b@\@citeb}{{\normalfont\bfseries ?}%
       \G@refundefinedtrue
       \@latex@warning
         {Citation `\@citeb' on page \thepage \space undefined}}%
       {{\csname b@\@citeb\endcsname}}}}{#1}}

\newenvironment{theindex}
  {\xhead*{\indexname}%
   \addcontentsline{toc}{section}{\indexname}%
   \footnotesize\normalfont \parindent\z@ \parskip\z@ \@plus .1\p@\relax
   \let\item\@idxitem}
  {\relax}

\newcommand\@idxitem  {\par\hangindent 1em}
\newcommand\subitem   {\par\hangindent 3em\hspace*{1em}}
\newcommand\subsubitem{\par\hangindent 4em \hspace*{2em}}
\newcommand\indexspace{\par\vskip\baselineskip \relax}

\renewcommand\footnoterule{% FROM LATEX.LTX
  \kern-3\p@
  \hrule\@width.4\columnwidth \@height\z@
  \kern 3\p@}

\def\@makefnmark{\@textsuperscript{\normalfont\@thefnmark}} % FROM LATEX.LTX

\newcommand\@makefntext[1]{%
  \@setpar{\@@par\@tempdima \hsize
    \advance\@tempdima-\oneem
    \parshape \@ne \oneem \@tempdima}\par
  \noindent \hb@xt@\z@{\hss\@makefnmark\ }#1}

\renewcommand\thefootnote{\@fnsymbol\c@footnote}

\def\@fnsymbol#1{\ensuremath{\ifcase#1\or \dagger\or \ddagger\or % FROM LATEX.LTX
  \mathsection\or \mathparagraph\or \|\or \dagger\dagger\or \ddagger\ddagger\or
  \mathsection\mathsection\or \mathparagraph\mathparagraph\or \|\| \else
  \@ctrerr\fi\relax}}

\setcounter{topnumber}{2}
\setcounter{bottomnumber}{1}
\setcounter{totalnumber}{3}
\setcounter{dbltopnumber}{2}
\renewcommand\topfraction{.9}
\renewcommand\bottomfraction{.9}
\renewcommand\textfraction{.1}
\renewcommand\floatpagefraction{.75}
\renewcommand\dbltopfraction{.9}
\renewcommand\dblfloatpagefraction{.5}

\newif\if@contcap
\let\@@caption\caption
\newcommand\contcaption{\@contcaptrue\addtocounter{\@captype}{-1}\@@caption}

\long\def\@makecaption#1#2{\vskip 6.5\p@
  \raggedright\sloppy #1\if@contcap {\normalfont\itshape\ continued}\fi.\ #2\par
  \@contcapfalse
}

\newcounter{table}
\renewcommand\thetable{\@arabic\c@table}

\def\fps@table{tbp}
\def\ftype@table{1}
\def\ext@table{lot}
\def\fnum@table{\tablename\ \thetable}

\newenvironment{table}
  {\@float{table}}
  {\end@float}
\newenvironment{table*}
  {\let\SFB@currenthline=\SFB@fullhline
   \@dblfloat{table}}
  {\end@dblfloat}

\def\fstyle@table{\footnotesize\normalfont\rmfamily}
\def\fjust@table{\raggedright}
\def\fcapjust@table{\raggedright\sloppy}
\def\fcapsize@table{\normalsize\normalfont\rmfamily}
\def\fcapstyle@table{\normalsize\normalfont\itshape}

\newcounter{figure}
\renewcommand\thefigure{\@arabic\c@figure}

\def\fps@figure{tbp}
\def\ftype@figure{2}
\def\ext@figure{lof}
\def\fnum@figure{\figurename\ \thefigure}

\newenvironment{figure}
  {\@float{figure}}
  {\end@float}
\newenvironment{figure*}
  {\@dblfloat{figure}}
  {\end@dblfloat}

\def\fstyle@figure{\small\normalfont\rmfamily}
\def\fjust@figure{\raggedright}
\def\fcapjust@figure{\raggedright\sloppy}
\def\fcapsize@figure{\small\normalfont\rmfamily}
\def\fcapstyle@figure{\small\normalfont\rmfamily}

\newif\ifwide@float

\long\def\@caption#1[#2]#3{%  FROM LATEX.LTX
  \par
  \addcontentsline{\csname ext@#1\endcsname}{#1}%
    {\protect\numberline{\csname the#1\endcsname}{\ignorespaces #2}}%
  \begingroup
    \ifwide@float \@parboxrestore\else \@myparboxrestore\fi
    \if@minipage
      \@setminipage
    \fi
    \@makecaption{\csname fcapjust@#1\endcsname \csname fcapsize@#1\endcsname
      \csname fnum@#1\endcsname}
      {\csname fcapstyle@#1\endcsname \ignorespaces #3}\par
  \endgroup}

\def\@xfloat #1[#2]{% FROM LATEX.LTX
%  \@nodocument
  \def \@captype {#1}%
   \def \@fps {#2}%
   \@onelevel@sanitize \@fps
   \def \reserved@b {!}%
   \ifx \reserved@b \@fps
     \@fpsadddefault
   \else
     \ifx \@fps \@empty
       \@fpsadddefault
     \fi
   \fi
   \ifhmode
     \@bsphack
     \@floatpenalty -\@Mii
   \else
     \@floatpenalty-\@Miii
   \fi
  \ifinner
     \@parmoderr\@floatpenalty\z@
  \else
    \@next\@currbox\@freelist
      {%
       \@tempcnta \sixt@@n
       \expandafter \@tfor \expandafter \reserved@a
         \expandafter :\expandafter =\@fps
         \do
          {%
           \if \reserved@a h%
             \ifodd \@tempcnta
             \else
               \advance \@tempcnta \@ne
             \fi
           \fi
           \if \reserved@a t%
             \@setfpsbit \tw@
           \fi
           \if \reserved@a b%
             \@setfpsbit 4%
           \fi
           \if \reserved@a p%
             \@setfpsbit 8%
           \fi
           \if \reserved@a !%
             \ifnum \@tempcnta>15
               \advance\@tempcnta -\sixt@@n\relax
             \fi
           \fi
           }%
       \@tempcntb \csname ftype@\@captype \endcsname
       \multiply \@tempcntb \@xxxii
       \advance \@tempcnta \@tempcntb
       \global \count\@currbox \@tempcnta
       }%
    \@fltovf
  \fi
  \global \setbox\@currbox
    \color@vbox
      \normalcolor
      \vbox \bgroup
        \hsize\columnwidth
        \ifwide@float
          \@parboxrestore \linewidth\textwidth
        \else
          \advance\hsize -2pc \@rightskip 2pc%
          \@myparboxrestore \linewidth\hsize
        \fi
        \@floatboxreset
        \csname fstyle@#1\endcsname \csname fjust@#1\endcsname
}

\def\@myarrayparboxrestore{%
  \let\if@nobreak\iffalse
  \let\if@noskipsec\iffalse
  \let\par\@@par
  \let\-\@dischyph
  \let\'\@acci\let\`\@accii\let\=\@acciii
  \parindent\z@ \parskip\z@skip
  \everypar{}%
  \linewidth\hsize
  \@totalleftmargin\z@
  \leftskip\z@skip \rightskip\@rightskip
  \parfillskip\@flushglue \lineskip\normallineskip
  \baselineskip\normalbaselineskip
  \sloppy}

\def\@myparboxrestore{\@myarrayparboxrestore\let\\\@normalcr}

\let\@@dblfloat\@dblfloat
\def\@dblfloat{\wide@floattrue\@@dblfloat}% FROM LATEX.LTX

\let\@@end@dblfloat\end@dblfloat
\def\end@dblfloat{\@@end@dblfloat\wide@floatfalse}% FROM LATEX.LTX

\def\SFB@fullhline{%
  \noalign{\ifnum0=`}\fi
  \vskip 3\p@
  \hrule \@height\arrayrulewidth \@width\textwidth
  \vskip 3\p@
  \futurelet \@tempa\@xhline
}

\def\SFB@hline{%
  \noalign{\ifnum0=`}\fi
  \vskip 3\p@
  \hrule \@height \arrayrulewidth
  \vskip 3\p@
  \futurelet \@tempa\@xhline
}

\let\SFB@currenthline=\SFB@hline

\renewcommand\hline{% FROM LATEX.LTX
  \noalign{\ifnum0=`}\fi
  \vskip 6\p@
  \hrule \@height \arrayrulewidth
  \vskip 6\p@
  \futurelet \@tempa\@xhline
}

\def\@xhline{%
  \ifx\@tempa\hline
    \vskip -12\p@
    \vskip \doublerulesep
  \fi
  \ifnum0=`{\fi}%
}

\let\SFB@currenthline\SFB@hline

\renewcommand\tabular{\let\@halignto\@empty % FROM LATEX.LTX
  \let\hline\SFB@currenthline
  \def\@xhline{%
    \ifx\@tempa\hline
      \vskip -6\p@
      \vskip \doublerulesep
    \fi
    \ifnum0=`{\fi}%
  }
  \def\@arrayrule{\@addtopreamble{\hskip -.5\arrayrulewidth
%                 \vrule \@width \arrayrulewidth
                  \hskip .5\arrayrulewidth}}%
  \@tabular}

\newcommand\ls{\kern.15em}
\newcommand\ns{\kern.5em}

\newcommand\contentsname{Contents}
\newcommand\listfigurename{List of figures}
\newcommand\listtablename{List of tables}
\newcommand\refname{References}
\newcommand\indexname{Index}
\newcommand\figurename{Fig.}
\newcommand\tablename{Table}
\newcommand\appendixname{Appendix}
\newcommand\today{}
\edef\today{\number\day\ \ifcase\month\or
  January\or February\or March\or April\or May\or June\or
  July\or August\or September\or October\or November\or December\fi
  \ \number\year
}

\pagestyle{headings}
\pagenumbering{arabic}
\flushbottom
\frenchspacing

\endinput

% End of file mscs.cls
