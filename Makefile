all: Makefile.coq
	$(MAKE) -f Makefile.coq all

tests:
	$(MAKE) -C tests

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -C tests clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@

.PHONY: all clean tests
