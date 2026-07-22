(* OpsComp.v - Computational transfer functions for the ZIntervalCongruence
   single-value abstraction. This is the executable core, destined to be
   extracted 1:1 to OCaml.

   STATUS: computational (no proofs). Soundness and α-completeness of these
   functions live in the matching [*Theory.v] files (e.g. [AddTheory.v]). *)

Require Import
  base Abstraction AbstractLattice
  AbstractionCombination
  Z_interval Congruence
  ZIntervalCongruence
  Transfer_function.ZInterval.AddTheory
  Transfer_function.Congruence.OpsComp.

(** ** Z.add transfer function (raw).

    [add_raw] adds the interval and congruence components independently.
    Each component operation ([interval_add], [cong_add]) is itself
    α-complete (best), so the resulting pair is already the best
    abstraction of the collecting sum — it is maximally reduced, and no
    [reduce] is needed afterwards. See [AddTheory.add],
    [AddTheory.add_raw_alpha_complete] and [AddTheory.add_alpha_complete]. *)
Definition add_raw (a2 a1 : prod_ajsl) : prod_ajsl :=
  let (i2, c2) := a2 in
  let (i1, c1) := a1 in
  (interval_add i2 i1, cong_add c2 c1).
