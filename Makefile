all: Makefile.coq
	export TIMED
	@+$(MAKE) -f Makefile.coq all

html: all Makefile.coq
	@+$(MAKE) -f Makefile.coq html
	mv html/*.html website
	rm -rf html

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

install: all
	@+$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all html clean force  
