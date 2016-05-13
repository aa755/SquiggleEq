all:
	make -f Makefile.coq

Makefile.coq : _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

install :
	make -f Makefile.coq install

_CoqProject:
	echo "-R . SquiggleLazyEq" > _CoqProject
	find . -name "*.v" >> _CoqProject
