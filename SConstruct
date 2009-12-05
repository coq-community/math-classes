import os, glob, string

nodes = ['.']
dirs = []
vs = []

while nodes:
  node = nodes.pop()
  b = os.path.basename(node)
  if node.endswith('.v'):
    vs += [node]
  if os.path.isdir(node):
    dirs += [node]
    nodes += glob.glob(node + '/*')

Rs = ' -R interfaces interfaces -R theory theory -R orders orders '
Rs_and_Is = Rs + ' -I implementations -I misc '

coqc = 'coqc ' + Rs_and_Is + ' $SOURCE'

env = DefaultEnvironment(ENV = os.environ)
env.Append(BUILDERS = {'Coq' : Builder(action = coqc, suffix = '.vo', src_suffix = '.v')})

env.Command('doc', vs,
  [Mkdir('doc'), 'coqdoc --no-lib-name -d $TARGET' + Rs + '$SOURCES'])

for node in vs:
  vo = env.Coq(node)
  env.Clean(vo, node[:-2] + '.glob')

os.system('coqdep ' + Rs_and_Is + ' '.join(vs) + ' > deps')
ParseDepends('deps')

Default(['implementations', 'theory'])
