SHELL := /bin/bash
LAKE ?= elan run $(shell tr -d '\r\n' < lean/lean-toolchain) lake
ROCQ ?= rocq

.PHONY: all lean rocq rocq-coquelicot foundations foundations-coquelicot clean cleanLean cleanRocq
all: lean rocq

lean:
	cd lean && $(LAKE) build
	cd lean && $(LAKE) env lean examples/Smoke.lean
	cd lean && $(LAKE) env lean examples/ProjectUse.lean
	cd lean && $(LAKE) env lean Textbook/Ch03/WorkedLimits.lean
	cd lean && $(LAKE) env lean Textbook/Ch03/RestrictedExamples.lean

rocq:
	@version="$$($(ROCQ) --print-version)"; case "$$version" in "9.2 "*|"9.2.0 "*) ;; *) echo "This project requires Rocq 9.2.0; found: $$version" >&2; exit 1;; esac
	cd rocq && $(ROCQ) makefile -f _CoqProject -o RocqMakefile
	$(MAKE) -C rocq -f RocqMakefile

rocq-coquelicot: rocq
	cd rocq && $(ROCQ) compile -Q AppendixA AppendixA AppendixA/CoquelicotSmoke.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch02/CoquelicotBridge.v

clean: cleanLean cleanRocq

# Textbook chapters 1–13; existing modules keep their stable paths.
foundations:
	cd lean && $(LAKE) build Textbook Textbook.Ch02.Sets Textbook.Ch02.Neighborhoods
	cd lean && $(LAKE) env lean Textbook/Ch03/DefinitionExamples.lean
	cd lean && $(LAKE) env lean Textbook/Ch03/WorkedLimits.lean
	cd lean && $(LAKE) env lean Textbook/Ch03/RestrictedExamples.lean
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch01/Language.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch02/Eventually.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch02/Reciprocal.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch02/Sets.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch02/Neighborhoods.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch03/LocalEstimates.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch02/Filters.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch02/Logic.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch03/StandardFilters.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch03/Approach.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch03/LimitRules.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch05/Sequences.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch04/LocalLimits.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch04/OneSidedInfinity.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch04/LimitRules.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch06/Derivatives.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch07/Differentiation.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch08/Taylor.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch03/Maps.v

foundations-coquelicot: foundations
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch02/CoquelicotBridge.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch03/CoquelicotBridge.v
	cd rocq && $(ROCQ) compile -Q Textbook Textbook Textbook/Ch09/Integration.v

cleanLean:
	cd lean && $(LAKE) clean filterCalculus

cleanRocq:
	cd rocq && $(ROCQ) makefile -f _CoqProject -o RocqMakefile
	$(MAKE) -C rocq -f RocqMakefile clean

# Current textbook, chapters 01-13 (including the Coquelicot integral chapter).
CHAPTER ?= 03
.PHONY: check check-lean check-rocq chapter chapter-lean chapter-rocq release
check: check-lean check-rocq
check-lean:
	cd lean && $(LAKE) build FilterCalculus
	cd lean && $(LAKE) env lean examples/Smoke.lean
	cd lean && $(LAKE) env lean examples/ProjectUse.lean
	cd lean && $(LAKE) env lean Textbook/Ch03/DefinitionExamples.lean
	cd lean && $(LAKE) env lean Textbook/Ch03/BasicExamples.lean
	cd lean && $(LAKE) env lean Textbook/Ch03/WorkedLimits.lean
	cd lean && $(LAKE) env lean Textbook/Ch03/RestrictedExamples.lean
check-rocq:
	cd rocq && $(ROCQ) makefile -f _CoqProjectTextbook -o TextbookMakefile
	$(MAKE) -C rocq -f TextbookMakefile
	cd rocq/templates/rocq-paths && $(ROCQ) makefile -f _CoqProject -o RocqMakefile
	$(MAKE) -C rocq/templates/rocq-paths -f RocqMakefile
chapter: chapter-lean chapter-rocq
chapter-lean:
	@case "$(CHAPTER)" in 01|02|03|04|05|06|07|08|09|10|11|12|13) ;; *) echo 'Use CHAPTER=01 through 13' >&2; exit 2;; esac
	cd lean && $(LAKE) build Textbook.Ch$(CHAPTER).All
chapter-rocq:
	@case "$(CHAPTER)" in 01|02|03|04|05|06|07|08|09|10|11|12|13) ;; *) echo 'Use CHAPTER=01 through 13' >&2; exit 2;; esac
	cd rocq && $(ROCQ) makefile -f _CoqProjectTextbook -o TextbookMakefile
	$(MAKE) -C rocq -f TextbookMakefile Textbook/Ch$(CHAPTER)/All.vo
release:
	python3 scripts/package-release.py
