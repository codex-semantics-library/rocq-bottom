# Convenience wrapper around the dune build (see dune-project / dune).
# dune is the real build system; every target just forwards to it.

.PHONY: all clean doc tags validate artifact

# No CPU cap by default, as a slow machine could hang on it with a baffling
# error message. This is useful during development (e.g. firstorder proofs can
# be slow); set it here or compile with make CPU_LIMIT=30
CPU_LIMIT ?=

all:
	$(if $(CPU_LIMIT),ulimit -t $(CPU_LIMIT); )dune build

debug-build:
	dune build --display=verbose -j 1

# Whole-theory HTML documentation, generated into doc/.
#
# Rocq 9.0 ships only the `rocq` driver: there is no standalone `coqdoc` binary,
# including in the rocq-prover Docker image. dune's @doc alias looks for one, so
# we invoke `rocq doc` ourselves. We run it inside _build/default, where dune has
# placed the sources next to the .glob files that coqdoc needs for cross-references.
doc: all
	@mkdir -p doc
	@cd _build/default && rocq doc -g -toc --utf8 -R . RocqBottom \
	  -d "$(CURDIR)/doc" $$(find . -name '*.v' | sort)
	@echo "Documentation generated in doc/"

clean:
	dune clean

# Emacs TAGS. Kept out of the dune build on purpose: coqtags is not part of the
# Rocq 9 driver and is absent from the Docker image, and a dune rule naming it is
# built by the default alias, which would fail the build there.
tags:
	coqtags $$(find . -name '*.v' \
	  -not -path './_build/*' -not -path './clean/*' -not -path './publication/*' | sort)

# Axiom-independence check: assert the library relies on no axioms. `rocqchk`
# (the kernel proof-checker, formerly coqchk; `rocq check` is broken in 9.0.1)
# with -o reports the axioms the whole closure depends on; we fail unless empty.
# Like `tags`, dune has no equivalent.
validate: all
	@set -e; \
	build=_build/default; \
	mods=$$(find $$build -name '*.vo' \
	         | sed -e "s|^$$build/||" -e 's|\.vo$$||' -e 's|/|.|g' -e 's|^|RocqBottom.|'); \
	echo "Checking axiom-independence of:"; echo "$$mods" | sed 's/^/  /'; \
	out=$$(cd $$build && rocqchk -o -R . RocqBottom $$mods 2>&1); \
	echo "$$out" | sed -n '/CONTEXT SUMMARY/,$$p'; \
	if echo "$$out" | grep -qx '\* Axioms: <none>'; then \
	  echo "OK: library is axiom-independent."; \
	else \
	  echo "FAIL: the checked closure depends on axioms (see the Axioms list above)."; \
	  echo "      A likely cause is 'Require Import Psatz' pulling in Stdlib.Reals;"; \
	  echo "      switch the offending file to 'Require Import Lia'."; \
	  exit 1; \
	fi

# Release tarball for archival (Zenodo). Built with `git archive`, so what ships
# is exactly the committed tree minus the export-ignore entries in .gitattributes
# Refuses to run on a dirty tree: the tarball must correspond to a commit, so the
# archived artifact and the paper's line numbers refer to the same snapshot.
ARTIFACT_NAME    := rocq-bottom
ARTIFACT_REF     ?= HEAD
ARTIFACT_VERSION ?= $(shell git describe --tags --always)
ARTIFACT_DIR     := $(ARTIFACT_NAME)-$(ARTIFACT_VERSION)
ARTIFACT_TARBALL := $(ARTIFACT_DIR).tar.gz

artifact:
	@git diff-index --quiet HEAD -- || { \
	  echo "make artifact: the working tree has uncommitted changes."; \
	  echo "               Commit them first: the tarball must match a commit."; \
	  exit 1; }
	@git archive --format=tar.gz --prefix=$(ARTIFACT_DIR)/ \
	   -o $(ARTIFACT_TARBALL) $(ARTIFACT_REF)
	@echo "Wrote $(ARTIFACT_TARBALL) from $$(git rev-parse --short $(ARTIFACT_REF))"
	@echo
	@echo "Contents:"
	@tar tzf $(ARTIFACT_TARBALL) | sed 's|^$(ARTIFACT_DIR)/||' | grep -v '^$$' | sort | sed 's/^/  /'
