all: Makefile.coq
	$(MAKE) -f Makefile.coq all

tests:
	PRINT_LOGS=1 $(MAKE) -C tests

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@

.PHONY: all clean tests
