#originall copied from https://github.com/math-classes/math-classes

import os, glob, string

dirs_to_compile = ['.']

nodes = map(lambda x: './' + x, dirs_to_compile)
dirs = []
vs = []


env = DefaultEnvironment(ENV = os.environ, tools=['default','Coq'])

while nodes:
  node = nodes.pop()
  b = os.path.basename(node)
  if (node.endswith('.v')
   and not node.endswith('universe-type.v')
   and not node.endswith('variables.v')):
    vs += [File(node)]
  if os.path.isdir(node):
    dirs += [node]
    nodes += glob.glob(node + '/*')

includes = ' '.join(map(lambda x: '-I ' + x, dirs[1:]))

Rs = '-R . SquiggleLazyEq'
coqcmd = 'coqc ${str(SOURCE)[:-2]} ' + Rs

env['COQFLAGS'] = Rs

for node in vs: env.Coq(node, COQCMD=coqcmd)


os.system('coqdep ' + ' '.join(map(str, vs)) + ' ' + includes + ' ' + Rs + ' > deps')
ParseDepends('deps')


#open('coqidescript', 'w').write('#!/bin/sh\ncoqide ' + Rs + ' $@ \n')
#os.chmod('coqidescript', 0755)



# Only after a normal build (for .vos) is complete, one can enable the 2 lines below to enable coqdoc generation (using scons coqdoc).  dont forget to then patch the generated HTML to disable caching. run patchNoCache.sh in the generated coqdoc/ directory. also see updateDoc.sh
# enabling it before somehow messes the dependency analysis done by scons
#mc_vs, mc_vos, mc_globs = env.SConscript(dirs='dependencies/corn/') # CoRN + MathClasses
env.CoqDoc(env.Dir('coqdoc'), vs, COQDOCFLAGS='-utf8 --toc --interpolate --no-lib-name --coqlib http://coq.inria.fr/library')
