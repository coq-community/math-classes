import os

env = DefaultEnvironment(ENV = os.environ, tools=['default', 'Coq'])
(vs, vos, globs) = env.SConscript(dirs='.')

env['COQFLAGS'] = Rs = ' -R . MathClasses '

Default('implementations', 'theory', 'categories', 'orders', 'varieties', 'misc', 'functors')

env.CoqDoc(env.Dir('coqdoc'), vs, COQDOCFLAGS='-utf8 --toc -g --no-lib-name http://coq.inria.fr/library')
  # Todo: Do "patch --backup $TARGET/coqdoc.css ../tools/coqdoc.css.diff", including the dependency on the .diff file.
  # Note: The generated documentation is no good, because of Coq bug #2423.

vs_string = ' '.join(map(str, vs))

os.system('coqdep ' + Rs + vs_string + ' > deps')
ParseDepends('deps')

open('coqidescript', 'w').write('#!/bin/sh\ncoqide ' + Rs + ' $@ \n')
os.chmod('coqidescript', 0755)

env.Command('deps.dot', [], '../tools/DepsToDot.hs < deps > $TARGET')
