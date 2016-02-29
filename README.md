# SquiggleLazyEq

An SConstruct file is provided for compilation using SCons (http://www.scons.org/).

In addition, an SCons library for Coq is needed. 
This can be achieved by copying 
the directory https://github.com/aa755/ROSCoq/tree/master/site_scons to either the root of this project,
or globally to ~/.scons

The main file so far is alphaeq.v
You can compile it using `scons alphaeq.vo`
