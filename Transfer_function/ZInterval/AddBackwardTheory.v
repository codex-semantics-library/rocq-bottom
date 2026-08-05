(* AddBackwardTheory.v - Backward (refinement) transfer functions for [Z.add]
   and [Z.sub] on the ZInterval single-value abstraction.

   The whole derivation is two steps:

     1. Concrete step. [Z.add] and [Z.sub] are invertible in each argument, so
        the backward collecting semantics is an intersection with forward
        collecting semantics ([collecting_binary_backward_{left,right}_inverse]).

     2. Abstract step. The meet of intervals is exact ([itv_meet_exact]) and the
        forward transfer functions of the inverses are exact on non-empty
        operands ([interval_add_exact], [interval_sub_exact]), so the composite
        is exact ([backward_binary_{left,right}_exact_of_inverse]).

   Each of the four transfer functions below is therefore three lines: name the
   inverse, discharge the inverse law by [lia], and cite the two exactness
   results. Nothing about bounds, [Top] or sign cases appears.

   STATUS:
   - add backward left/right: exact ([backward_interval_add_{left,right}_exact]);
   - sub backward left/right: exact ([backward_interval_sub_{left,right}_exact]); 
   both stated as [ternary_exact] on [nbitv] operands, and both available through the
   [option]-pair refinement interface ([impl_backward_interval_{add,sub}_correct]).

   - α-completeness is false [backward_add_not_alpha_complete],
   because [α] does not distribute over [∩]. *)

Require Import Abstraction AbstractLattice.
Require Import ssreflect ssrbool ssrfun.
Require Import BoundAbstraction.
Require Import AbstractionCombination.
Require Import BoundLattice.
Require Import autoreflect.
Require Import Tactics.
Require Import Quadrivalent.
From Stdlib Require Import Lia.
Require Import Stdlib.ZArith.ZArith.
Require Import ZInterval.
Require Import ZIntervalTheory.
Require Import Transfer_function.ZInterval.ZIntervalOps.
Require Import Transfer_function.ZInterval.ZIntervalBackwardOps.
Require Import Transfer_function.ZInterval.AddTheory.
Require Import Transfer_function.ZInterval.BackwardInterfaceTheory.
Open Scope Z_scope.
Generalizable All Variables.

(** * The inverse laws.

    The only arithmetic content of the whole file. Each says that one
    argument of the operation can be recovered from the result and the
    other argument. *)

Lemma Zadd_inverse_left  c2 c1 c0 : c2 + c1 = c0 <-> c0 - c1 = c2.
Proof. lia. Qed.

Lemma Zadd_inverse_right c2 c1 c0 : c2 + c1 = c0 <-> c0 - c2 = c1.
Proof. lia. Qed.

Lemma Zsub_inverse_left  c2 c1 c0 : c2 - c1 = c0 <-> c0 + c1 = c2.
Proof. lia. Qed.

Lemma Zsub_inverse_right c2 c1 c0 : c2 - c1 = c0 <-> c2 - c0 = c1.
Proof. lia. Qed.


(** * The transfer functions.

    Each is stated in [ternary_exact] form on [nbitv] operands — the
    intervals the analyzer normally holds. The *result* stays on the raw
    [itv] carrier: a backward step that detects a contradiction must be
    able to return a γ-empty interval, so it cannot land in [nbitv].

    On a concrete [exist _ i H], [γ[nbitv]] reduces to [γ[itv] i]
    ([Subset.gamma] is a match on the pair), so destructing the three
    operands turns each statement into its raw form, which is what the
    generic derivation discharges. *)

(** * Backward [Z.add]. *)

Section Backward_add.

(** [c2] is recovered as [c0 - c1], so the abstract transfer function is [i2 ⊓
    (i0 - i1)]. Note that [i2] itself is unconstrained: it is only intersected,
    so it may be γ-empty without harming exactness. ([i0] and [i1]) are the ones
    that must be non-empty, since that is what [interval_sub_exact] needs. *)
Lemma backward_interval_add_left_exact :
  ternary_exact nbitv nbitv nbitv itv backward_interval_add_left
    (collecting_binary_backward_left Z.add).
Proof.
  move=> [i2 H2] [i1 H1] [i0 H0].
  exact: (backward_binary_left_exact_of_inverse itv itv itv
            Z.add Z.sub Zadd_inverse_left        (* c2 + c1 = c0 <-> c0 - c1 = c2 *)
            interval_sub ZInterval.meet itv_meet_exact (* abstract inverse; exact meet  *)
            i2 i1 i0 (interval_sub_exact i0 i1 H0 H1)).
Qed.

(** Symmetrically, [c1 = c0 - c2], giving [i1 ⊓ (i0 - i2)]. *)
Lemma backward_interval_add_right_exact :
  ternary_exact nbitv nbitv nbitv itv backward_interval_add_right
    (collecting_binary_backward_right Z.add).
Proof.
  move=> [i2 H2] [i1 H1] [i0 H0].
  exact: (backward_binary_right_exact_of_inverse itv itv itv
            Z.add Z.sub Zadd_inverse_right        (* c2 + c1 = c0 <-> c0 - c2 = c1 *)
            interval_sub ZInterval.meet itv_meet_exact
            i2 i1 i0 (interval_sub_exact i0 i2 H0 H2)).
Qed.

End Backward_add.


(** * Backward [Z.sub]. *)

Section Backward_sub.

(** [c2 = c0 + c1], giving [i2 ⊓ (i0 + i1)]. *)
Lemma backward_interval_sub_left_exact :
  ternary_exact nbitv nbitv nbitv itv backward_interval_sub_left
    (collecting_binary_backward_left Z.sub).
Proof.
  move=> [i2 H2] [i1 H1] [i0 H0].
  exact: (backward_binary_left_exact_of_inverse itv itv itv
            Z.sub Z.add Zsub_inverse_left         (* c2 - c1 = c0 <-> c0 + c1 = c2 *)
            interval_add ZInterval.meet itv_meet_exact
            i2 i1 i0 (interval_add_exact i0 i1 H0 H1)).
Qed.

(** The one asymmetric case: the inverse recovering [c1] from [c2 - c1 =
    c0] is [fun c0 c2 => c2 - c0], i.e. [Z.sub] with its arguments
    flipped, so the abstract side is [i1 ⊓ (i2 - i0)] and the exactness
    hypothesis needs [collecting_binary_forward_flip] to line the two
    operand sets up. *)
Lemma backward_interval_sub_right_exact :
  ternary_exact nbitv nbitv nbitv itv backward_interval_sub_right
    (collecting_binary_backward_right Z.sub).
Proof.
  move=> [i2 H2] [i1 H1] [i0 H0].
  have Hg : γ[itv] (interval_sub i2 i0) ⊆⊇
            collecting_binary_forward (fun c0 c2 => c2 - c0) (γ[itv] i0) (γ[itv] i2).
  { rewrite (collecting_binary_forward_flip Z.sub).
    exact: (interval_sub_exact i2 i0 H2 H0). }
  exact: (backward_binary_right_exact_of_inverse itv itv itv
            Z.sub (fun c0 c2 => c2 - c0) Zsub_inverse_right
            (fun a0 a2 => interval_sub a2 a0) ZInterval.meet itv_meet_exact
            i2 i1 i0 Hg).
Qed.

End Backward_sub.


(** * α-completeness on arbitrary sets fails.

    The reason is structural rather than accidental: the derivation replaces the
    backward collecting semantics by an intersection, and [α] does not
    distribute over [∩] (intervals are not a "meet-complete" abstraction —
    [α({0,2} ∩ {1,3}) = ⊥] while [α{0,2} ⊓ α{1,3} = [0,2] ⊓ [1,3] = [1,2]]).

    The witness below is exactly that: [S2 = {0}], [S1 = {0,2}], [S0 =
    {1,3}]. The backward set is empty (no element of [S1] is in [S0]), yet the
    transfer function returns [[1,2]], which is not the best abstraction of
    [∅]. *)

(** The operands' non-bottomness is part of their type, so the witnesses
    and examples below have to supply it. [nb i] is [i] with that proof
    found by [lia] (or by [done], for the [Top] bounds where
    [non_bottom] is [True]). *)
Local Definition nbI (i : interval) (H : non_bottom i) : nb_interval := exist _ i H.
Local Notation nb i := (nbI i ltac:(by simpl; try lia)) (only parsing).

Section Alpha_incompleteness.

Local Definition S2 : ℘ Z := {[ z | z = 0 ]}.
Local Definition S1 : ℘ Z := {[ z | z = 0 \/ z = 2 ]}.
Local Definition S0 : ℘ Z := {[ z | z = 1 \/ z = 3 ]}.

Local Lemma alpha_S2 : IsAlpha (A:=itv) (WithTop.NotTop 0, WithTop.NotTop 0) S2.
Proof. apply: is_alpha_itv_attained; rewrite /S2; unfold_set; lia. Qed.

Local Lemma alpha_S1 : IsAlpha (A:=itv) (WithTop.NotTop 0, WithTop.NotTop 2) S1.
Proof. apply: is_alpha_itv_attained; rewrite /S1; unfold_set; lia. Qed.

Local Lemma alpha_S0 : IsAlpha (A:=itv) (WithTop.NotTop 1, WithTop.NotTop 3) S0.
Proof. apply: is_alpha_itv_attained; rewrite /S0; unfold_set; lia. Qed.

(** No [c1 ∈ S1] is reachable: [c2 ∈ S2] is [0], so [c1] would have to
    lie in [S0] too, and [S1 ∩ S0 = ∅]. *)
Local Lemma backward_set_empty :
  collecting_binary_backward_right Z.add S2 S1 S0 ⊆⊇ ∅.
Proof.
  unfold_set_equiv => c1; unfold_set; split => //.
  move=> [c2 [c0 [Hc2 [Hc1 [Hc0 Heq]]]]].
  move: Hc2 Hc1 Hc0. rewrite /S2 /S1 /S0. unfold_set. lia.
Qed.

Example backward_add_not_alpha_complete :
  ~ (forall (i2 i1 i0 : nb_interval) (T2 T1 T0 : ℘ Z),
        IsAlpha (A:=itv) (`i2) T2 -> IsAlpha (A:=itv) (`i1) T1 ->
        IsAlpha (A:=itv) (`i0) T0 ->
        IsAlpha (A:=itv) (backward_interval_add_right i2 i1 i0)
          (collecting_binary_backward_right Z.add T2 T1 T0)).
Proof.
  move=> Hac.
  (* At these operands the transfer function returns
     [[0,2] ⊓ ([1,3] - [0,0])] = [[0,2] ⊓ [1,3]] = [[1,2]]. *)
  have H := Hac (nb (WithTop.NotTop 0, WithTop.NotTop 0))
                (nb (WithTop.NotTop 0, WithTop.NotTop 2))
                (nb (WithTop.NotTop 1, WithTop.NotTop 3))
                _ _ _ alpha_S2 alpha_S1 alpha_S0.
  move: H => /(is_alpha_set_equiv _ _ _ backward_set_empty) H.
  (* [IsAlpha a ∅] would force [a ⊑ b] for *every* [b]; [[5,4]] refutes it. *)
  have := proj1 (H (WithTop.NotTop 5, WithTop.NotTop 4)) (fun c Hc => match Hc with end).
  by move=> /is_includedP.
Qed.

End Alpha_incompleteness.


(** * The low-level refinement interface.

    All that is left to check is the [option] protocol — [None] exactly when
    nothing was learned — and [impl_backward_itv_correct] discharges that once
    and for all, from the fact that a meet refines the operand it is taken with
    ([itv_meet_lower_bound_l]). *)

Lemma impl_backward_interval_add_correct :
  backward_itv_correct impl_backward_interval_add
    backward_interval_add_left backward_interval_add_right.
Proof.
  apply: impl_backward_itv_correct => i2 i1 i0; exact: itv_meet_lower_bound_l.
Qed.

Lemma impl_backward_interval_sub_correct :
  backward_itv_correct impl_backward_interval_sub
    backward_interval_sub_left backward_interval_sub_right.
Proof.
  apply: impl_backward_itv_correct => i2 i1 i0; exact: itv_meet_lower_bound_l.
Qed.


(** * The interface at work.

    All four behaviours the refinement interface must exhibit, checked by
    computation. *)

Local Notation N := WithTop.NotTop.

(** Refining one operand: from [[0,0] + [0,2] = [1,3]] we learn nothing
    about the left operand, and that the right one is in [[1,2]]. *)
Example backward_add_refines_right :
  impl_backward_interval_add (nb (N 0, N 0)) (nb (N 0, N 2)) (nb (N 1, N 3))
  = (None, Some (N 1, N 2)).
Proof. reflexivity. Qed.

(** Nothing to learn: [[0,1] + [0,1] = [0,2]] is already consistent. *)
Example backward_add_learns_nothing :
  impl_backward_interval_add (nb (N 0, N 1)) (nb (N 0, N 1)) (nb (N 0, N 2))
  = (None, None).
Proof. reflexivity. Qed.

(** Contradiction: [[0,1] + [0,1]] can never be [5]. Both operands are
    refined to a γ-empty interval — the reason the result of a backward
    transfer function cannot live in [nbitv]. *)
Example backward_add_detects_contradiction :
  impl_backward_interval_add (nb (N 0, N 1)) (nb (N 0, N 1)) (nb (N 5, N 5))
  = (Some (N 4, N 1), Some (N 4, N 1))
  /\ ~ non_bottom (N 4, N 1).
Proof. split; [reflexivity | rewrite /non_bottom; lia]. Qed.

(** Backward [sub] on an unconstrained operand: [[1,2] - x = 0] pins [x]
    down to [[1,2]] out of [Top]. *)
Example backward_sub_refines_top :
  impl_backward_interval_sub (nb (N 1, N 2)) (nb itv_top) (nb (N 0, N 0))
  = (None, Some (N 1, N 2)).
Proof. reflexivity. Qed.
