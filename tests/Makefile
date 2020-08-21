# Mostly taken from https://github.com/coq/coq/blob/master/test-suite/

#######################################################################
# Variables
#######################################################################

SHELL := /bin/bash

PACKAGE := coq-dblib
COQEXTRAFLAGS ?=
COQFLAGS ?= $(COQEXTRAFLAGS)
LIBS ?= $(shell cat _CoqProject)
PREREQUISITES := $(shell find $(shell echo $(LIBS) | sed -E 's/^-. ([^ ]+) .+/\1/') -regex '.*\.vo?')

coqc := coqc -q $(LIBS) $(COQFLAGS)
coqchk := coqchk $(LIBS)
coqdoc := coqdoc
coqtop := coqtop -q -test-mode $(LIBS)
coqtopbyte := coqtop.byte -q

coqc_interactive := $(coqc) -test-mode -async-proofs-cache force
coqdep := coqdep

# This is the convention for coq_makefile
OPT=-opt
export OPT

VERBOSE?=
SHOW := $(if $(VERBOSE),@true,@echo)
HIDE := $(if $(VERBOSE),,@)
REDIR := $(if $(VERBOSE),,> /dev/null 2>&1)

# read out an emacs config and look for coq-prog-args; if such exists, return it
get_coq_prog_args_helper = sed -n s'/^.*coq-prog-args:[[:space:]]*(\([^)]*\)).*/\1/p' $(1)
get_coq_prog_args = $(strip $(shell $(call get_coq_prog_args_helper,$(1))))
SINGLE_QUOTE="
#" # double up on the quotes, in a comment, to appease the emacs syntax highlighter
# wrap the arguments in parens, but only if they exist
get_coq_prog_args_in_parens = $(subst $(SINGLE_QUOTE),,$(if $(call get_coq_prog_args,$(1)), ($(call get_coq_prog_args,$(1)))))

# keep these synced with test-suite/save-logs.sh
log_success = "==========> SUCCESS <=========="
log_warning = "==========> WARNING <=========="
log_segfault = "==========> FAILURE <=========="
log_anomaly = "==========> FAILURE <=========="
log_failure = "==========> FAILURE <=========="
log_intro = "==========> TESTING $(1) <=========="

FAIL = >&2 echo 'FAILED    $@'

#######################################################################
# Testing subsystems
#######################################################################

BUGS := bugs/opened bugs/closed
VSUBSYSTEMS := $(BUGS) success failure

# All subsystems
SUBSYSTEMS := $(VSUBSYSTEMS)

#######################################################################
# Phony targets
#######################################################################

.DELETE_ON_ERROR:
.PHONY: run clean $(SUBSYSTEMS)

run: $(SUBSYSTEMS) report

clean:
	rm -f trace output/MExtraction.out
	rm -f vos/Makefile vos/Makefile.conf
	find . \( -regex '.*\.\(stamp\|vo\|vio\|vos\|vok\|log\|glob\|aux\|[ln][ir]a\.cache\)' \) -exec rm -f {} +

#######################################################################
# Per-subsystem targets
#######################################################################

define vdeps
$(1): $(patsubst %.v,%.v.log,$(wildcard $(1)/*.v))
endef
$(foreach S,$(VSUBSYSTEMS),$(eval $(call vdeps,$(S))))

#######################################################################
# Summary
#######################################################################

summary_dir = echo $(1); [ ! -x $(2) ] || find $(2) -name '*.log' -print0 | xargs -0 -n 1 tail -n1 | sort

.PHONY: report summary.log

report: summary.log
	$(HIDE)bash report.sh

summary.log:
	$(SHOW) BUILDING SUMMARY FILE
	@{ \
	  $(call summary_dir, "Bugs tests", bugs); \
	  $(call summary_dir, "Success tests", success); \
	  $(call summary_dir, "Failure tests", failure); \
	  nb_success=`find . -name '*.log' -exec tail -n2 '{}' \; | grep -e $(log_success) -e $(log_warning) | wc -l`; \
	  nb_failure=`find . -name '*.log' -exec tail -n2 '{}' \; | grep -e $(log_failure) | wc -l`; \
	  nb_tests=`expr $$nb_success + $$nb_failure`; \
	  nb_tests_nonzero=`[ $$nb_tests -gt 0 ] && echo $$nb_tests || echo 1` \
	  percentage=`expr 100 \* $$nb_success / $$nb_tests_nonzero`; \
	  echo; \
	  echo "$$nb_success tests passed over $$nb_tests, i.e. $$percentage %"; \
	} > "$@"

#######################################################################
# Regression (and progression) tests
#######################################################################

# Process verifications concerning submitted bugs. A message is
# printed for all opened bugs (still active or seems to be closed).
# For closed bugs that behave as expected, no message is printed

# All files are assumed to have <# of the bug>.v as a name

# Opened bugs that should not fail
$(addsuffix .log,$(wildcard bugs/opened/*.v)): %.v.log: %.v $(PREREQUISITES)
	@echo "TEST      $<  $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(coqc) "$<" $(call get_coq_prog_args,"$<") 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...still active"; \
	  elif [ $$R = 129 ]; then \
	    echo $(log_anomaly); \
	    echo "    $<...still active"; \
	  elif [ $$R = 139 ]; then \
	    echo $(log_segfault); \
	    echo "    $<...still active"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (bug seems to be closed, please check)"; \
	    $(FAIL); \
	  fi; \
	} > "$@"

# Closed bugs that should succeed
$(addsuffix .log,$(wildcard bugs/closed/*.v)): %.v.log: %.v $(PREREQUISITES)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(coqc) "$<" $(call get_coq_prog_args,"$<") 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (bug seems to be opened, please check)"; \
	    $(FAIL); \
	  fi; \
	} > "$@"

#######################################################################
# Other generic tests
#######################################################################

# Success tests
$(addsuffix .log,$(wildcard success/*.v)): %.v.log: %.v $(PREREQUISITES)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  opts="$(if $(findstring modules/,$<),-R modules Mods)"; \
	  echo $(call log_intro,$<); \
	  $(coqc) "$<" $(call get_coq_prog_args,"$<") $$opts 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (should be accepted)"; \
	    $(FAIL); \
	  fi; \
	} > "$@"
	@if ! grep -q -F "Error!" $@; then echo "CHECK     $<"; fi
	$(HIDE)if ! grep -q -F "Error!" $@; then { \
	  $(coqchk) -silent $(call get_set_impredicativity,$<) $(if $(findstring modules/,$<),-R modules Mods -norec Mods.$(shell basename $< .v),-Q $(shell dirname $<) "" -norec $(shell basename $< .v)) 2>&1; R=$$?; \
	  if [ $$R != 0 ]; then \
	    echo $(log_failure); \
	    echo "    $<...could not be checked (Error!)" ; \
	    $(FAIL); \
	  fi; \
	} > "$(shell dirname $<)/$(shell basename $< .v).chk.log"; fi

# Failure tests
$(addsuffix .log,$(wildcard failure/*.v)): %.v.log: %.v $(PREREQUISITES)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(coqc) "$<" $(call get_coq_prog_args,"$<") 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (should be rejected)"; \
	    $(FAIL); \
	  fi; \
	} > "$@"
	@if ! grep -q -F "Error!" $@; then echo "CHECK     $<"; fi
	$(HIDE)if ! grep -q -F "Error!" $@; then { \
	  $(coqchk) -silent -Q $(shell dirname $<) "" -norec $(shell basename $< .v) 2>&1; R=$$?; \
	  if [ $$R != 0 ]; then \
	    echo $(log_failure); \
	    echo "    $<...could not be checked (Error!)" ; \
	    $(FAIL); \
	  fi; \
	} > "$(shell dirname $<)/$(shell basename $< .v).chk.log"; fi
