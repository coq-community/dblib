all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

tests:
	@+$(MAKE) -C tests

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@+$(MAKE) -C tests clean
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force tests
