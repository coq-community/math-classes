# -*- coding: utf-8 -*-

import SCons.Defaults, SCons.Tool, SCons.Util, os

def add_glob(target, source, env):
  base, _ = os.path.splitext(str(target[0]))
  target.append(base + ".glob")
  return target, source

Coq = SCons.Builder.Builder(
  action = '$COQC $COQFLAGS -q  $SOURCE',
  suffix = '.vo',
  src_suffix = '.v',
  emitter = add_glob)

def generate(env):
  env['COQC'] = 'coqc'
  env.Append(BUILDERS = {'Coq': Coq})

def exists(env):
  return env.Detect('coqc')

