(* QuadrivalentAPI.v - Export layer for the quadrivalent domain: checks the
   domain against the ABSTRACT_DOMAIN / ABSTRACT_LATTICE signatures and
   groups the boolean transfer functions behind them.

   The signatures span both layers ([t], [is_included], [join], [meet],
   [equal] are computational; [ad] and [ad_car_ad_eq_t] are not), so the
   conformance checks live here rather than in [QuadrivalentComp.v].

   The extraction directives are in [ocaml/quadrivalentextract.v], which
   must sit next to the generated OCaml for dune's [coq.extraction]. *)

Require Import Abstraction AbstractLattice.
Require Import QuadrivalentComp QuadrivalentTheory.
Require Import Transfer_function.Quadrivalent.OpsComp.

Module QuadrivalentCheck <: ABSTRACT_DOMAIN := QuadrivalentTheory.
Module QuadrivalentLatticeCheck <: ABSTRACT_LATTICE := QuadrivalentTheory.
