(* MulBackwardTheory.v - Backward (refinement) transfer function for [Z.mul] on
   the ZInterval single-value abstraction.

   Follow calculational style : we split the backward collecting semantics into
   "incoming set ∩ solve set", then handle the solve set. [Z.mul] admits no inverse:

     - at [c2 = 0] every [c1] satisfies [0 * c1 = 0], so no function can recover
       [c1] from [c0] and [c2];
     - elsewhere [c1 = c0 ÷ c2] holds only when [c2] divides [c0],
       and intervals cannot express divisibility in general.

   Some special case of divisibility (e.g. constants) could be handled, but we 
   let the congruence operation deal with it, and we target soundness only here.
   Still, we implement an optimized version (fast-pathing the case where nothing
   can be learned), by proving equivalence with the unoptimized version
   [impl_backward_interval_mul_eq].

   STATUS: mul (Z.mul) backward left/right: sound, and reasonably precise. *)

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
Require Import PrimitiveTheory.
Require Import Transfer_function.ZInterval.ZIntervalOps.
Require Import Transfer_function.ZInterval.ZIntervalBackwardOps.
Require Import Transfer_function.ZInterval.QuotTheory.
Require Import Transfer_function.ZInterval.AddBackwardTheory.
Require Import Transfer_function.ZInterval.BackwardInterfaceTheory.
Open Scope Z_scope.
Generalizable All Variables.

(** * The solve step.

    Everything specific to multiplication lives here: the abstract
    operation over-approximating

      [{c1 | ∃ c2 ∈ γ i2, c0 ∈ γ i0, c2 * c1 = c0}].

    No hypotheses are needed — the operand intervals are non-empty
    because the solve set exhibits members of both. *)

Lemma interval_mul_solve_sound (i2 : nb_interval) (i0 : interval) :
  Overapproximates (A:=itv) (interval_mul_solve i2 i0)
    (collecting_binary_solve_right Z.mul (γ[itv] (` i2)) (γ[itv] i0)).
Proof.
  move=> c1 Hc1. unfold_set in Hc1.
  move: Hc1 => [c2 [c0 [Hc2 [Hc0 Heq]]]].
  rewrite /interval_mul_solve.
  case Hg: (mul_solve_is_top (` i2) i0); first by unfold_set.
  move: Hg; rewrite /mul_solve_is_top => Hg.
  (* The guard failed, so [c2 = 0] is impossible: it would force
     [c0 = 0], putting [0] in both [γ i2] and [γ i0]. *)
  have Hc2n0 : c2 <> 0.
  { move=> Hz. move: Heq. rewrite Hz Z.mul_0_l => Hc00.
    move: Hg.
    have -> : itv_gammab (` i2) 0 = true by apply/itv_gammaP; rewrite -Hz.
    have -> : itv_gammab i0 0 = true by apply/itv_gammaP; rewrite Hc00.
    done. }
  (* [c2] divides [c0] exactly, so truncated division recovers [c1]. *)
  have Hquot : c1 = Z.quot c0 c2.
  { by rewrite -Heq Z.mul_comm Z.quot_mul. }
  (* [c1] is therefore a member of the quotient's collecting semantics. *)
  have Hmem : c1 ∈ collecting_quot (γ[itv] i0) (γ[itv] (` i2))
    by unfold_set; exists c0, c2.
  (* Division by zero is excluded, since [c2 ∈ γ i2] with [c2 ≠ 0]. *)
  have HnZ : classify_divisor i2 <> DivZero
    by move=> HDZ; exact: (classify_divisor_zero_empty i2 _ _ HDZ Hmem).
  have Hnb0 : non_bottom i0 by apply/non_bottom_non_empty; exists c0.
  have [Hover _] := interval_quot_best i0 i2 Hnb0 HnZ.
  exact: Hover.
Qed.


(** * Backward [Z.mul]. *)

(** The soundness and precision lemmas below are stated on the [_unopt] versions
    — the direct solve-then-meet transcription — because that is the shape the
    generic calculus of [Abstraction.v] discharges. The optimized versions
    ([backward_interval_mul_right] / [_left]) are proved equal to them by
    [backward_interval_mul_{right,left}_eq] just below, so they inherit
    soundness ([backward_interval_mul_{right,left}_sound] below restate it for
    the optimized names) and the precision examples are unaffected since they
    compute the same result. *)

Lemma backward_interval_mul_right_unopt_sound :
  ternary_overapproximation nbitv nbitv nbitv itv backward_interval_mul_right_unopt
    (collecting_binary_backward_right Z.mul).
Proof.
  (* [γ[nbitv]] only reduces to [γ[itv]] on an explicit pair. *)
  move=> [i2 H2] [i1 H1] [i0 H0].
  exact: (backward_binary_right_sound_of_solver nbitv itv itv Z.mul
            interval_mul_solve ZInterval.meet
            (fun a b => proj2 (itv_meet_exact a b))
            (exist _ i2 H2) i1 i0 (interval_mul_solve_sound (exist _ i2 H2) i0)).
Qed.

(** The left refinement is the right one on the swapped operands; the
    only thing to check is that the two collecting semantics agree,
    which is [collecting_binary_backward_left_comm] at [Z.mul_comm]. *)
Lemma backward_interval_mul_left_unopt_sound :
  ternary_overapproximation nbitv nbitv nbitv itv backward_interval_mul_left_unopt
    (collecting_binary_backward_left Z.mul).
Proof.
  move=> i2 i1 i0.
  rewrite /Overapproximates (collecting_binary_backward_left_comm Z.mul Z.mul_comm).
  exact: (backward_interval_mul_right_unopt_sound i1 i2 i0).
Qed.


(** * The optimized transfer functions equal the unoptimized ones.

    [backward_interval_mul_right] skips the meet when the solve set is
    [⊤] (returning the incoming operand unchanged); the unoptimized
    [backward_interval_mul_right_unopt] performs that meet, which is the
    identity on [⊤]. The two are thus equal by case on the guard, and
    the soundness lemmas above carry over directly. *)

Lemma backward_interval_mul_right_eq (i2 i1 i0 : nb_interval) :
  backward_interval_mul_right i2 i1 i0 = backward_interval_mul_right_unopt i2 i1 i0.
Proof.
  move: i1 => [[i1l i1h] Hi1].
  destruct i1l as [|i1l]; destruct i1h as [|i1h].
  all: rewrite /backward_interval_mul_right /backward_interval_mul_right_unopt
              /interval_mul_solve /refine_by;
        case: (mul_solve_is_top (`i2) (`i0));
        [by rewrite /ZInterval.meet /= | by []].
Qed.

Lemma backward_interval_mul_left_eq (i2 i1 i0 : nb_interval) :
  backward_interval_mul_left i2 i1 i0 = backward_interval_mul_left_unopt i2 i1 i0.
Proof.
  rewrite /backward_interval_mul_left /backward_interval_mul_left_unopt
          backward_interval_mul_right_eq. done.
Qed.

(** Soundness of the optimized versions, by equality with the unoptimized
    ones. *)
Lemma backward_interval_mul_right_sound :
  ternary_overapproximation nbitv nbitv nbitv itv backward_interval_mul_right
    (collecting_binary_backward_right Z.mul).
Proof.
  move=> i2 i1 i0. rewrite /Overapproximates
    (backward_interval_mul_right_eq i2 i1 i0).
  exact: (backward_interval_mul_right_unopt_sound i2 i1 i0).
Qed.

Lemma backward_interval_mul_left_sound :
  ternary_overapproximation nbitv nbitv nbitv itv backward_interval_mul_left
    (collecting_binary_backward_left Z.mul).
Proof.
  move=> i2 i1 i0. rewrite /Overapproximates
    (backward_interval_mul_left_eq i2 i1 i0).
  exact: (backward_interval_mul_left_unopt_sound i2 i1 i0).
Qed.


(** * Precision: sound, not exact, and not best.

    Backward multiplication is not exact — and the obstruction is
    divisibility, not a weakness of the derivation. From [2 * c1 = 1]
    there is no integer solution, so the backward set is empty; but
    [[1,1] ÷ [2,2] = [0,0]] is the best an interval can say, since [0]
    genuinely is the truncated quotient.

    It is also not best, and the [solve]-then-[meet] shape cannot be made
    so. Two independent sources of loss (brute-forced at ~20% of small
    boxes):

    - *Divisibility.* [interval_mul_solve] returns the truncated-quotient
      set, not the solve set [T = {c1 | ∃ c2 ∈ γi2, c0 ∈ γi0, c2·c1 = c0}].
      [backward_interval_mul_not_exact] is the [T = ∅] instance;
      [backward_interval_mul_not_best] states the non-optimality directly.

    - *Meet vs non-convex [T].* Even with a perfect [hull(T)], refining by
      [meet i1] re-admits hull-only points, since
      [hull(γi1 ∩ hull(T)) ≠ hull(γi1 ∩ T)] when [T] is non-convex — e.g.
      [i2 = [2,4]], [i0 = [8,8]] give [T = {2,4}] (3 ∤ 8), and with
      [i1 = [3,5]] the meet yields [[3,4]] while the true best is [[4,4]].

    Best is achievable (intervals are a Galois connection, so [hull(S)] always
    exists) but only as a *joint* [hull(γi1 ∩ T)] computation over the sign
    regions of [c1] and [c2], not as [solve]-then-[meet]. The divisibility half
    is recovered by the interval × congruence product, which expresses residues. *)

(** The operands' non-bottomness is now part of their type, so the
    examples below have to supply it. [nb i] is [i] with that proof found
    by [lia] (or by [done], for the [Top] bounds where [non_bottom] is
    [True]). *)
Local Definition nbI (i : interval) (H : non_bottom i) : nb_interval := exist _ i H.
Local Notation nb i := (nbI i ltac:(by simpl; try lia)) (only parsing).

Example backward_interval_mul_not_exact :
  ~ ExactlyRepresents (A:=itv)
      (backward_interval_mul_right_unopt
         (nb (WithTop.NotTop 2, WithTop.NotTop 2)) (nb itv_top)
         (nb (WithTop.NotTop 1, WithTop.NotTop 1)))
      (collecting_binary_backward_right Z.mul
         (γ[itv] (WithTop.NotTop 2, WithTop.NotTop 2)) (γ[itv] itv_top)
         (γ[itv] (WithTop.NotTop 1, WithTop.NotTop 1))).
Proof.
  move=> [Hunder _].
  (* [0] is in the abstract result … *)
  have H0 : 0 ∈ γ[itv] (backward_interval_mul_right_unopt
                          (nb (WithTop.NotTop 2, WithTop.NotTop 2)) (nb itv_top)
                          (nb (WithTop.NotTop 1, WithTop.NotTop 1)))
    by solve_with_autoreflect.
  (* … but the concrete backward set is empty: [2 * c1 = 1] has no solution. *)
  have := Hunder _ H0. unfold_set.
  move=> [c2 [c0 [Hc2 [_ [Hc0 Heq]]]]].
  unfold_set in Hc2; unfold_set in Hc0; simpl in *; lia.
Qed.

(** Same operands, the bestness statement: the result is *not* the best
    abstraction of the backward set. [IsAlpha αS S] is the Galois-connection
    form of "αS is the best abstraction of S" (cf. [is_alpha_iff_best_abstraction]);
    it fails here because the backward set is empty while the result is the
    non-empty [[0,0]]. This is the divisibility source of the loss — see the
    section header for the second, structural one. *)
Example backward_interval_mul_not_best :
  ~ IsAlpha (A:=itv)
      (backward_interval_mul_right_unopt
         (nb (WithTop.NotTop 2, WithTop.NotTop 2)) (nb itv_top)
         (nb (WithTop.NotTop 1, WithTop.NotTop 1)))
      (collecting_binary_backward_right Z.mul
         (γ[itv] (WithTop.NotTop 2, WithTop.NotTop 2)) (γ[itv] itv_top)
         (γ[itv] (WithTop.NotTop 1, WithTop.NotTop 1))).
Proof.
  move=> /(_ (WithTop.NotTop 5, WithTop.NotTop 4)) [Hle _].
  (* The concrete backward set is empty: [2 * c1 = 1] has no solution. *)
  have Hsub : collecting_binary_backward_right Z.mul
                (γ[itv] (WithTop.NotTop 2, WithTop.NotTop 2)) (γ[itv] itv_top)
                (γ[itv] (WithTop.NotTop 1, WithTop.NotTop 1))
              ⊆ γ[itv] (WithTop.NotTop 5, WithTop.NotTop 4).
  { move=> c1 Hc1. unfold_set in Hc1.
    move: Hc1 => [c2 [c0 [Hc2 [_ [Hc0 Heq]]]]].
    unfold_set in Hc2; unfold_set in Hc0; simpl in *.
    have Hc2e : c2 = 2 by lia.
    have Hc0e : c0 = 1 by lia.
    exfalso. lia. }
  (* [IsAlpha] would force [backward_interval_mul_right_unopt …] ⊑ [[5,4]];
     the result computes to [[0,0]], but [[5,4]] is γ-empty ([5 > 4]),
     so [[0,0]] ⊑ [[5,4]] is false. *)
  have Hle' : (WithTop.NotTop 0, WithTop.NotTop 0) ⊑[itv]
              (WithTop.NotTop 5, WithTop.NotTop 4).
  { rewrite /backward_interval_mul_right_unopt /refine_by /interval_mul_solve.
    rewrite /mul_solve_is_top /itv_gammab /ZInterval.glb_gammab
            /ZInterval.lub_gammab /=; simpl.
    exact: Hle Hsub. }
  move: Hle' => /is_includedP. simpl. done.
Qed.


(** * The low-level refinement interface. *)

(** Both refinements are a meet, so the [option] protocol is the generic
    one — including on the left, which is the right refinement on the
    swapped operands and therefore meets with [i2]. The optimized right
    refinement returns the incoming operand unchanged in the
    [mul_solve_is_top] branch (still a lower bound of itself); the
    other branch is a meet as before. *)
Lemma backward_interval_mul_right_lower_bound (i2 i1 i0 : nb_interval) :
  backward_interval_mul_right i2 i1 i0 ⊑[itv] (`i1).
Proof.
  rewrite (backward_interval_mul_right_eq i2 i1 i0).
  exact: itv_meet_lower_bound_l.
Qed.

Lemma backward_interval_mul_left_lower_bound (i2 i1 i0 : nb_interval) :
  backward_interval_mul_left i2 i1 i0 ⊑[itv] (`i2).
Proof.
  rewrite (backward_interval_mul_left_eq i2 i1 i0).
  exact: itv_meet_lower_bound_l.
Qed.

(** The optimized interface equals the unoptimized one component-wise:
    each [refine_itv] in the optimized version takes the same interval
    that [refine_by] produces in the unoptimized one (the [⊤] branch of
    the guard is the identity meet, so both feed [refine_itv] the same
    operand). *)
Lemma impl_backward_interval_mul_eq (i2 i1 i0 : nb_interval) :
  impl_backward_interval_mul i2 i1 i0 = impl_backward_interval_mul_unopt i2 i1 i0.
Proof.
  (* The optimized impl bypasses [refine_by] in the [⊤] branch (returning
     [None] directly) and otherwise wraps the same meet in [refine_itv].
     The component equalities [backward_interval_mul_{right,left}_eq]
     reduce the unopt impl to the opt component functions; then each
     [refine_itv (if … then `i else meet …)] agrees with the opt
     [(if … then None else refine_itv …)] because [refine_itv i i = None]
     ([itv_equalP] on a reflexive equality). *)
  have Hrefl : forall i : interval, refine_itv i i = None.
  { move=> i. rewrite /refine_itv.
    case: (itv_equalP i i) => [_|H]; last by exfalso; apply: H; reflexivity.
    by []. }
  rewrite /impl_backward_interval_mul /impl_backward_interval_mul_unopt
          /impl_backward_itv /backward_mul_refine
          (eq_sym (backward_interval_mul_left_eq i2 i1 i0))
          (eq_sym (backward_interval_mul_right_eq i2 i1 i0))
          /backward_interval_mul_left /backward_interval_mul_right.
  f_equal.
  - (* left: guard on i1 (swapped). *)
    case: (mul_solve_is_top (` i1) (` i0)).
    + exact: (eq_sym (Hrefl (` i2))).
    + by rewrite /refine_itv.
  - (* right: guard on i2. *)
    case: (mul_solve_is_top (` i2) (` i0)).
    + exact: (eq_sym (Hrefl (` i1))).
    + by rewrite /refine_itv.
Qed.

(** The unoptimized interface is correct by the same argument (the meet
    is always a lower bound); stated for completeness, since the
    optimized one is the one exposed. *)
Lemma impl_backward_interval_mul_unopt_correct :
  backward_itv_correct impl_backward_interval_mul_unopt
    backward_interval_mul_left_unopt backward_interval_mul_right_unopt.
Proof.
  apply: impl_backward_itv_correct => i2 i1 i0; exact: itv_meet_lower_bound_l.
Qed.

Lemma impl_backward_interval_mul_correct :
  backward_itv_correct impl_backward_interval_mul
    backward_interval_mul_left backward_interval_mul_right.
Proof.
  move=> i2 i1 i0.
  rewrite (impl_backward_interval_mul_eq i2 i1 i0)
          (backward_interval_mul_left_eq i2 i1 i0)
          (backward_interval_mul_right_eq i2 i1 i0).
  exact: (impl_backward_interval_mul_unopt_correct i2 i1 i0).
Qed.


(** * The interface at work. *)

Local Notation N := WithTop.NotTop.

(** [[3,3] * x = [7,9]] pins [x] down to [[2,3]]. *)
Example backward_mul_refines :
  impl_backward_interval_mul (nb (N 3, N 3)) (nb itv_top) (nb (N 7, N 9))
  = (None, Some (N 2, N 3)).
Proof. reflexivity. Qed.

(** The zero guard. [0 * x] can be [0] for any [x], so nothing at all is
    learned — and in particular the result is *not* [interval_quot],
    which would have answered [ZInterval.bottom] here and been unsound. *)
Example backward_mul_zero_learns_nothing :
  impl_backward_interval_mul (nb (N 0, N 0)) (nb (N 3, N 8)) (nb (N 0, N 0))
  = (None, None).
Proof. reflexivity. Qed.

(** With [0] excluded from the result, [c2 = 0] becomes impossible, the
    divisor is sanitized, and the left operand loses its zero:
    [x * y = 12] with [y ∈ [1,3]] forces [x ∈ [4,10]]. *)
Example backward_mul_excludes_zero :
  impl_backward_interval_mul (nb (N 0, N 10)) (nb (N 1, N 3)) (nb (N 12, N 12))
  = (Some (N 4, N 10), None).
Proof. reflexivity. Qed.

(** Sound but not exact, side by side. [2 * x = 1] has no solution: the
    left refinement does detect it (γ-empty [[2,1]]), but the right one
    only manages [[0,0]] — truncated division cannot see that [2] does
    not divide [1]. Cf. [backward_interval_mul_not_exact]. *)
Example backward_mul_asymmetric_precision :
  impl_backward_interval_mul (nb (N 2, N 2)) (nb itv_top) (nb (N 1, N 1))
  = (Some (N 2, N 1), Some (N 0, N 0))
  /\ ~ non_bottom (N 2, N 1).
Proof. split; [reflexivity | rewrite /non_bottom; lia]. Qed.
