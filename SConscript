
import os, glob, string

nodes = ['.']
dirs = []
vs = []

while nodes:
  node = nodes.pop()
  b = os.path.basename(node)
  if node.endswith('.v') and not b.endswith('_nobuild.v'):
    vs += [File(node)]
  if os.path.isdir(node) and b != 'broken':
    dirs += [node]
    nodes += glob.glob(node + '/*')

env = DefaultEnvironment()

vos = globs = []
for node in vs:
  vo, glob = env.Coq(node)
  vos += [vo]
  globs += [glob]

Return('vs vos globs')
