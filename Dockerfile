# Build with:  docker build -t rocq-bottom .
# Run with:    docker run --rm -it --network none rocq-bottom bash
#
# --network none is deliberate: on some Docker configurations, shell commands
# inside the container hang without it. See README.org.
#
# Inside the container:
#   make            # build the whole theory (dune)
#   make validate   # check the proofs rely on no axioms (no Admitted lemmas)
#   make doc        # generate the HTML documentation into doc/
#
# Pinned by digest rather than the floating `9.0` tag, so that this recipe keeps
# building the artifact as archived. 
FROM rocq/rocq-prover:9.0@sha256:787ea5569c9bf40e03a2255224365cb2fb0ae4a446fc60565dd61b1656d1699d
USER rocq
WORKDIR /home/rocq

# Rocq 9 is driver-based: the image provides `rocq` (and `rocqchk`), but none of
# the standalone `coqc` / `coqdep` / `coqdoc` / `coq_makefile` binaries. The dune
# it ships (3.17) still invokes `coqc` and `coqdep`, so bridge the two with thin
# shims onto the driver.
RUN mkdir -p /home/rocq/bin \
 && printf '#!/bin/sh\nexec rocq c "$@"\n'   > /home/rocq/bin/coqc \
 && printf '#!/bin/sh\nexec rocq dep "$@"\n' > /home/rocq/bin/coqdep \
 && printf '#!/bin/sh\nexec rocq doc "$@"\n' > /home/rocq/bin/coqdoc \
 && chmod +x /home/rocq/bin/coqc /home/rocq/bin/coqdep /home/rocq/bin/coqdoc
ENV PATH="/home/rocq/bin:${PATH}"

# The build is driven by dune (dune-project + dune) and the theory spans
# subdirectories (Transfer_function/, ocaml/), so copy the whole tree.
# .dockerignore keeps build output, the paper and the old artifact copy out.
COPY --chown=rocq:rocq . /home/rocq/
RUN make all
