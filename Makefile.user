# This is the main Makefile. It defines all dummy targets. It is also in
# charge of computing all dependencies before invoking the core Makefile.

# This Makefile is meant to be run sequentially.
MAKEFLAGS := -j1

# The local file "cores" should contain an appropriate option for
# parallelism, e.g. "-j4". If it is absent, only one core is used.

.PHONY: all clean

# --------------------------------------------------------------------------------

# Commands.

# Include directives.

COQC    := $(COQBIN)coqc -I .
COQDEP  := $(COQBIN)coqdep -I .

# --------------------------------------------------------------------------------

# Source and target files.

VFILES       := $(wildcard *.v)
VOFILES      := $(VFILES:.v=.vo)
DEPS         := $(VFILES:.v=.v.d)

# --------------------------------------------------------------------------------

# The default rule.

# We first compute all dependencies, then invoke the core Makefile in parallel mode.

all: $(DEPS)
	@ $(MAKE) COQC="$(COQC)" DEPS="$(DEPS)" -f Makefile.core `cat cores` $(VOFILES)

# --------------------------------------------------------------------------------

# Building dependencies.

%.v.d: %.v
	@ $(COQDEP) $< > $@

# --------------------------------------------------------------------------------

# Cleanup.

clean::
	rm -f *.vo *~ *.v.d *.glob .\#*

