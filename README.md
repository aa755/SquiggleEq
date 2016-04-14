# SquiggleLazyEq

An SConstruct file is provided for compilation using SCons (http://www.scons.org/).
On Ubuntu, scons can be installed using `sudo apt-get scons`. 
Cygwin also provides an scons package which I successfully use in Windows.

To compile, run `scons` in the root directory of the project.

After compilation, to use these files in other project use the flag `-R /local/path/to/this/repo SquiggleLazyEq`
