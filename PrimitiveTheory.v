(* PrimitiveTheory.v - Set-level facts about primitives. *)
Require Import Abstraction AbstractLattice.
Require Import ssreflect ssrbool ssrfun.
Require Import BoundAbstraction.
Require Import AbstractionCombination.
Require Import BoundLattice.
Require Import autoreflect.
Require Import Tactics.
Require Import Stdlib.Bool.Bool.
Require Import Quadrivalent.
From Stdlib Require Import Lia. (* lia/nia; avoid Psatz which loads Reals axioms *)
Require Import Stdlib.ZArith.ZArith.
Require Import ZInterval.
Require Import ZIntervalTheory.
Open Scope Z_scope.
Generalizable All Variables.

(** * Collecting semantics.

    The primitives in [Primitives.v] are partial: each requires a non-zero
    divisor.  Their forward collecting semantics are all the same generic
    [collecting_binary_forward_partial] instance: the "divisor is non-zero"
    predicate, the one that makes [Primitives.quot_non_zero] extraction sound;
    differing only in the concrete operation [f].  [collecting_non_zero_r]
    packages that shared predicate, and the three primitives are its
    instantiations. *)

Definition collecting_non_zero_r (f : Z -> Z -> Z) (S2 S1 : propset Z) : propset Z :=
  collecting_binary_forward_partial (fun _ c1 => c1 <> 0) f S2 S1.
Hint Unfold collecting_non_zero_r: to_set.

(** Truncating (C99) division [Z.quot]. *)
Definition collecting_quot (S2 S1 : propset Z) : propset Z :=
  collecting_non_zero_r Z.quot S2 S1.
Hint Unfold collecting_quot: to_set.

(** Floor division [Z.div]. *)
Definition collecting_div (S2 S1 : propset Z) : propset Z :=
  collecting_non_zero_r Z.div S2 S1.
Hint Unfold collecting_div: to_set.

(** Remainder of truncating division [Z.rem]. *)
Definition collecting_rem (S2 S1 : propset Z) : propset Z :=
  collecting_non_zero_r Z.rem S2 S1.
Hint Unfold collecting_rem: to_set.

(** Restricting the divisor to its nonzero elements leaves [collecting_quot]
    unchanged, so a ⊆⊇-equivalence between a divisor set and "divisors of [S1']
    distinct from 0" lifts to [collecting_quot].  Used by the dispatcher to
    relate the sanitized [DivPos] / [DivNeg] payload to the original divisor. *)
Lemma collecting_quot_restrict_equiv (S2 S1 S1' : propset Z) :
  S1 ⊆⊇ {[z | z ∈ S1' /\ z <> 0]} ->
  collecting_quot S2 S1 ⊆⊇ collecting_quot S2 S1'.
Proof.
  rewrite propset_equiv_iff => HE.
  unfold_set_equiv => z0.
  apply: exists_iff => c2; apply: exists_iff => c1.
  move: (HE c1); unfold_set; simpl. tauto.
Qed.

(** Splitting the right (divisor) operand at [< 0] / [0 <]: a strict cut that
    excludes [0]. *)
Lemma collecting_non_zero_split_zero_strict_r (f : Z -> Z -> Z) (S2 S1 : propset Z) :
  collecting_non_zero_r f S2 S1 ⊆⊇
  collecting_non_zero_r f S2 {[ z | z ∈ S1 /\ z < 0 ]} ∪
  collecting_non_zero_r f S2 {[ z | z ∈ S1 /\ 0 < z ]}.
Proof.
  unfold collecting_non_zero_r.
  apply: (collecting_binary_forward_partial_split_r
            (fun _ c1 => c1 <> 0) f S2 S1
            {[ z | z ∈ S1 /\ z < 0 ]} {[ z | z ∈ S1 /\ 0 < z ]}).
  - move=> c2 c1 Hc2 Hc1 Hne.
    unfold_set.
    case: (Z.le_gt_cases c1 0) => Hc1z; [left | right]; split=> //; lia.
  - unfold_set; by move=> c [Hc _].
  - unfold_set; by move=> c [Hc _].
Qed.
