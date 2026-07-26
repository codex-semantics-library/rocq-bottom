(* APICheck.v - Compile-time conformance check: certifies that the
   quadrivalent abstraction *is* an [ABSTRACT_DOMAIN] and an
   [ABSTRACT_LATTICE], by subtyping [QuadrivalentTheory] against the
   signatures. The build fails if the carrier or its lattice ops ever
   drift from the signatures.*)

Require Import Abstraction AbstractLattice.
Require Import Quadrivalent QuadrivalentTheory.

Module Check <: ABSTRACT_DOMAIN := QuadrivalentTheory.
Module LatticeCheck <: ABSTRACT_LATTICE := QuadrivalentTheory.
