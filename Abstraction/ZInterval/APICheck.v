(* APICheck.v - Compile-time conformance check: asserts by module subtyping that
   the interval abstraction's presentation [ZIntervalAPI] is an
   [NONEMPTY_ABSTRACT_LATTICE]. The build fails if its carriers or ops ever
   drift from the signatures.

   Not extracted, and Required by nothing: a pure assertion. *)

Require Import Abstraction AbstractLattice.
Require Import ZInterval ZIntervalTheory ZIntervalAPI.

Module Check <: NONEMPTY_ABSTRACT_DOMAIN := ZIntervalAPI.
Module LatticeCheck <: NONEMPTY_ABSTRACT_LATTICE := ZIntervalAPI.
