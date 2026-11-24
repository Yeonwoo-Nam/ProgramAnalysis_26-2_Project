.DEFAULT_GOAL := all
CORE_THEORIES := $(shell find src -iname '*.v' ! -path 'src/Examples/*' | sort)
EXAMPLE_THEORIES := $(shell find src/Examples -iname '*.v' | sort)
SUPPORTED_THEORIES := $(CORE_THEORIES) $(EXAMPLE_THEORIES)
THEORIES := $(SUPPORTED_THEORIES)

.PHONY: all core audit clean FORCE

FORCE:

all: Makefile.coq $(SUPPORTED_THEORIES)
	$(MAKE) -f Makefile.coq -j1 $(patsubst %.v,%.vo,$(SUPPORTED_THEORIES))

core: Makefile.coq $(CORE_THEORIES)
	$(MAKE) -f Makefile.coq -j1 $(patsubst %.v,%.vo,$(CORE_THEORIES))

audit: all
	coqtop -quiet -batch -R src DAnalyzer -l src/Examples/Assumptions.v
	coqchk -silent -R src DAnalyzer DAnalyzer.Abstract.TransitionSound DAnalyzer.Abstract.InterpreterSound DAnalyzer.Examples.Examples DAnalyzer.Examples.InterpreterExamples DAnalyzer.Examples.NonLatticeDomain

# Match FlowDown: discover sources on every invocation, but keep the project
# timestamp stable unless its contents change (including moves/removals).
_CoqProject: FORCE
	@(echo '-arg -w -arg -deprecated-hint-without-locality'; \
	 echo '-arg -w -arg -deprecated-instance-without-locality'; \
	 echo '-arg -w -arg -notation-incompatible-prefix'; \
	 echo '-arg -w -arg -notation-overriden'; \
	 echo '-arg -w -arg -ambiguous-paths'; \
	 echo '-arg -w -arg -redundant-canonical-projection'; \
	 echo '-arg -w -arg -cannot-define-projection'; \
	 echo '-R src DAnalyzer'; \
	 echo $(THEORIES)) > $@.tmp
	@if cmp -s $@.tmp $@; then \
	  rm -f $@.tmp; \
	else \
	  mv $@.tmp $@; \
	  rm -f .Makefile.coq.d; \
	fi

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	@if test -f Makefile.coq; then $(MAKE) -f Makefile.coq clean; fi
