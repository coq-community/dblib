# This is the main Makefile. It defines all dummy targets. It is also in
# charge of computing all dependencies before invoking the core Makefile.

# This Makefile is meant to be run sequentially.
MAKEFLAGS := -j1

.PHONY: all clean axioms wc shadow serious html export depend targets archive mezzo

# --------------------------------------------------------------------------------

# Define SERIOUS=1 or use "make serious" to check all proofs in the normal way.

# By default, SERIOUS is undefined. Then, the .v files are processed using coqj
# (which removes all proof scripts) so as to build dummy .vo files in the directory
# _shadow; these dummy .vo files are then used to check the proof scripts with
# maximum parellelism. This is useful on multi-core machines, but is not foolproof,
# as it (in principle) allows cyclic dependencies between files.

ifdef SERIOUS
SHADOW  := .
else
SHADOW  := _shadow
endif

# --------------------------------------------------------------------------------

# Commands.

# Include directives.

COQC    := $(COQBINDIR)coqc -I $(SHADOW)
COQDEP  := $(COQBINDIR)coqdep -I $(SHADOW)

# --------------------------------------------------------------------------------

# Source and target files.

VFILES       := $(wildcard *.v)
SHADOWVFILES := $(patsubst %.v,$(SHADOW)/%.v,$(VFILES))
VOFILES      := $(VFILES:.v=.vo)
GLOBFILES    := $(VFILES:.v=.glob)
HTFILES      := $(VFILES:.v=.html) index.html
DEPS         := $(VFILES:.v=.v.d) $(SHADOWVFILES:.v=.v.d)

# I distinguish between files that are mine and third-party files. Only the
# former are used by [make wc] and [make axioms].

THIRDPARTY := LibTactics.v
MINE       := $(shell ls *.v | grep -v $(THIRDPARTY))
NOAXIOMS   := $(shell ls *.v | grep -v $(THIRDPARTY))

# --------------------------------------------------------------------------------

# The default rule.

# We first compute all dependencies, then invoke the core Makefile in parallel mode.

all: $(DEPS)
	@ $(MAKE) COQC="$(COQC)" DEPS="$(DEPS)" -f Makefile.core `cat cores` $(VOFILES)

# --------------------------------------------------------------------------------

# Building dependencies.

# Like ocamldep, coqdep is broken insofar as it checks whether certain files exist
# (which does not make sense, since a file may not exist now but appear later if it
# is a compilation target). To work around this, we use ocamldep.wrapper, which
# creates phony files while coqdep runs and removes them immediately.

%.v.d: %.v
	@ /bin/mkdir -p $(SHADOW)
	@ ./ocamldep.wrapper $(SHADOWVFILES) - $(COQDEP) $< > $@

# --------------------------------------------------------------------------------

# How to create the shadow .v files. These files are obtained via coqj,
# a preprocessor that erases the proofs.

ifndef SERIOUS
.SECONDARY: $(SHADOWVFILES)

$(SHADOW)/%.v: %.v coqj
	@ /bin/mkdir -p $(SHADOW) && ./coqj $< > $@
endif

# --------------------------------------------------------------------------------

# Alternate entry points.

# The local file "cores" (not under version control) should contain an appropriate
# option for parallelism, e.g. "-j4".

# [make depend] builds the auxiliary dependency files.

depend: $(DEPS)

# [make targets] builds only the targets listed in the file "targets".

targets: $(DEPS)
	@ $(MAKE) COQC="$(COQC)" DEPS="$(DEPS)" -f Makefile.core `cat cores` `cat targets`

# [make shadow] re-builds all of the shadow [.vo] files (if necessary). It is
# useful for reaching a consistent state before opening Proof General.

shadow: $(DEPS)
	@ $(MAKE) COQC="$(COQC)" DEPS="$(DEPS)" -f Makefile.core `cat cores` $(SHADOWVFILES)

# [make serious] re-builds everything without using the shadow file hack. It
# is the recommended way of checking that everything is valid.

serious:
	$(MAKE) clean
	$(MAKE) SERIOUS=1 all

# [make axioms] looks for axioms or other forms of unproved statements.

axioms:
	@for keyword in Axiom "skip\\." Admitted Parameter Abort ; do \
	  if ! grep --line-number $$keyword $(NOAXIOMS) ; then \
	    echo "No $$keyword (good)." ; \
	  fi \
	done

# [make wc] measures the size of the development.

wc:
	@wc $(MINE)

# [make html] builds the HTML documentation.
# It invokes another sub-Makefile in parallel mode.

html: all
	@ $(MAKE) GLOBFILES="$(GLOBFILES)" -f Makefile.www `cat cores` $(HTFILES)

# [make archive] builds an archive of everything.

DATE     := $(shell /bin/date +%Y%m%d)
NAME     := dblib
ARCHIVE  := $(NAME)-$(DATE)

archive: # html
	rm -rf $(ARCHIVE) $(ARCHIVE).tar.gz
	mkdir $(ARCHIVE) && cp README LICENSE $(ARCHIVE)
	mkdir $(ARCHIVE)/src && cp *.v Makefile.core $(ARCHIVE)/src
	cp Makefile.user $(ARCHIVE)/src/Makefile
	echo "-j1" > $(ARCHIVE)/src/cores
#	mkdir $(ARCHIVE)/html && cp *.html *.css *.js $(ARCHIVE)/html
	tar cvfz $(ARCHIVE).tar.gz $(ARCHIVE)

# --------------------------------------------------------------------------------

# Export towards the Web site.

SERVER := yquem.inria.fr
WEBDIR := public_html/$(NAME)

export: archive
	ssh $(SERVER) "bash -c 'cd $(WEBDIR) && /bin/rm -f *.html'"
	scp README $(ARCHIVE).tar.gz $(SERVER):$(WEBDIR)
#	scp *.html *.css *.js $(SERVER):$(WEBDIR)
	ssh $(SERVER) "bash -c 'cd $(WEBDIR) && /bin/ln -sf $(ARCHIVE).tar.gz $(NAME).tar.gz'"

# Export towards the Mezzo development.

mezzo:
	cp -f MyTactics.v DeBruijn.v Environments.v $(HOME)/dev/mezzo/coq

# --------------------------------------------------------------------------------

# Building the preprocessor, [coqj].

%.ml: %.mll
	ocamllex $<

coqj: coqj.ml
	ocamlopt -o $@ $<

# --------------------------------------------------------------------------------

# Cleanup.

clean::
	rm -f *.vo *~ *.v.d *.glob *.html .\#*
	rm -f coqj.ml coqj *.cmi *.cmx *.o
	rm -f coq2html.ml coq2html
	rm -f coq2index.ml coq2index
	rm -f *.tex
	rm -f targets

ifndef SERIOUS
clean::
	rm -rf $(SHADOW)
endif


# --------------------------------------------------------------------------------
# coq_makefile support for install targets
#
# coq_makefile generates (sub)Makefile that distill the hard-won
# packaging knowledge of the Coq community. Using it for install
# targets help respect (evolving) best practices.

# inspired from http://adam.chlipala.net/cpdt/html/Large.html "Build Process"
MODULES := DeBruijn DblibTactics Environments
VS      := $(MODULES:%=%.v)
LIBRARY_NAME := Dblib # installation will go to user-contrib/$(LIBRARY_NAME)...

Makefile.coq_makefile: Makefile $(VS)
	coq_makefile -R . $(LIBRARY_NAME) $(VS) -o Makefile.coq_makefile

clean:: Makefile.coq_makefile
	$(MAKE) -f Makefile.coq_makefile clean
	rm -f Makefile.coq

install: Makefile.coq_makefile
	$(MAKE) -f Makefile.coq_makefile install
