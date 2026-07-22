(* AddTheory.v - [Z.add] and [Z.sub] transfer functions for the ZInterval
   single-value abstraction: [interval_add] / [interval_sub] on two intervals.
   Split out of Z_interval.v. *)

(* STATUS: add (Z.add): sound + best (α-complete)
     (interval_add_alpha_complete, nb_interval_add_exact);
   sub (Z.sub): sound + exact on non-bottom intervals (nb_interval_sub_exact).

   The generic α-machinery these proofs rest on (attainment witnesses,
   split-at-zero, [Z_interval_lift2_alpha_complete]) stays in ZIntervalTheory.v,
   since [MulTheory.v] needs it too.

   The extraction block at the end is provisional: per architecture.org the
   extraction directives belong in an export layer ([*API.v]), which does not
   exist yet. *)

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
Require Import ZIntervalTheory.
Require Import Transfer_function.ZInterval.OpsComp.
Require Import Transfer_function.ZInterval.OppTheory.
Open Scope Z_scope.
Generalizable All Variables.

Section Interval_add.

Lemma interval_add_sound:
  binary_overapproximation itv itv itv interval_add
    (collecting_binary_forward Z.add).
Proof.
  overapproximation_proof.
  move: a2 a1 Hc2_in_a2 Hc1_in_a1 => [[|l2] [|h2]] [[|l1] [|h1]] Hc2_in_a2 Hc1_in_a1;
  unfold_set; unfold_set in Hc2_in_a2; unfold_set in Hc1_in_a1; simpl in *; try lia.
Qed.

Example interval_add_not_exact:
  ~ (binary_exact itv itv itv interval_add (collecting_binary_forward Z.add)).
Proof.
  (* 4 belongs to [1,0] + [3,8], even if gamma([1,0]) is empty. *)
  set a2 := (WithTop.NotTop 1, WithTop.NotTop 0).
  set a1 := (WithTop.NotTop 3, WithTop.NotTop 8).  
  set c0 := 4.
  (* TODO: simplify; this should be dischargeable by computation. It needs a
     [forall]-style iterator over γ, so that finite sets can be computed and
     compared directly. *)
  assert(Hc0_in_intervaladd: c0 ∈ γ[itv] (interval_add a2 a1))
    by solve_with_autoreflect.
  move /(_ a2 a1). to_set.
  have HU := unfold_set_equiv. unfold_set.
  move /(_ c0). unfold γ.
  move=> H. apply H in Hc0_in_intervaladd.
  (* move: Hc0_in_intervaladd. *)
  unfold_set in Hc0_in_intervaladd. simpl in Hc0_in_intervaladd.
  move: Hc0_in_intervaladd => [c2 [c1 [Hc2_in_a2 [Hc1_in_a1 defc0]]]]; lia.
Qed.  

Definition nb_interval_add := non_bottom_lift_total_binary interval_add Z.add (Hsound:=interval_add_sound).

(** Completeness of non-bottom intervals. *)
Lemma nb_interval_add_gamma_complete:
  binary_underapproximation nbitv nbitv nbitv nb_interval_add
    (collecting_binary_forward Z.add).
Proof.
  move=> [i2 P2] [i1 P1] c0 Hc0.
  rewrite gamma_nbitv_gamma_itv /= in Hc0.
  have HU := unfold_set_equiv.
  move: i2 i1 P2 P1 Hc0 => [[|l2] [|h2]] [[|l1] [|h1]] P2 P1 Hc0;
  simpl in *; unfold_set in Hc0; unfold_set.
  Ltac finish := repeat split; lia.
  (* When the arguments are very unconstrained, a single witness
     suffices.  We fix c2/c1 to this bound and chose the other
     accordingly. When the interval is top, we arbitrarily chose 0 as
     the witness. *)
  all: try (exists c0, 0; finish).
  all: try (exists (c0 - h1), h1; finish).
  all: try (exists (c0 - l1), l1; finish).
  all: try (exists h2, (c0 - h2); finish).
  all: try (exists l2, (c0 - l2); finish).

  (* [l2,h2]+l1 and [l2,h2]+h1 always cover [l2+l1, h2+h1]: for any c0
     in the sum, either c0 ≤ l2+h1 (pick c2=l2, c1=c0-l2) or c0 ≥
     l2+h1 (pick c1=h1, c2=c0-h1). Both cases satisfy the bounds
     because l2 ≤ h2 and l1 ≤ h1.

     Similarly, either c0 <= l1 + h2, or c0 >= l1 + h2. Depending on
     where is the bound, we must choose one decomposition or the
     other (and both work when both intervals are finite). *)
  all: try (destruct (Z.le_ge_cases l1 (c0 - h2));
            [exists h2, (c0 - h2) | exists (c0 - l1), l1]; finish).
  all: destruct (Z.le_ge_cases (c0 - l2) h1);
    [exists l2, (c0 - l2) | exists (c0 - h1), h1]; finish.
Qed.

Lemma nb_interval_add_exact:
  binary_exact nbitv nbitv nbitv nb_interval_add
    (collecting_binary_forward Z.add).
Proof.
  move=> a2 a1; split.
  - apply nb_interval_add_gamma_complete.
  - apply non_bottom_lift_sound.
Qed.

(** ** Best abstraction for [interval_add] applied to abstract sets.

    Given [IsAlpha (l_i, h_i) S_i] for both operands, the resulting
    interval [interval_add (l_1,h_1) (l_2,h_2)] is the most precise
    abstraction of the Minkowski sum [{a + b | a ∈ S_1, b ∈ S_2}].

    The proof leverages the fact that [Z.add] admits an inverse
    (subtraction), so optimality follows without needing the glb/lub
    to be attained in [S_i]. Inhabitance of both sets is needed to
    constrain the result when bounds are infinite or to use the
    subtraction trick when bounds are finite. *)

(** Best abstraction for [interval_add] on abstract sets. Derived from the
    generic [Z_interval_lift2_alpha_complete]: casing the pair operands
    makes [interval_add] and [interval_lift2 Z.add] reduce to the same
    pair, so [apply:] can unify by conversion. *)
Lemma interval_add_alpha_complete (i2 i1 : interval) (S2 S1 : ℘ Z) :
  (exists c, c ∈ S2) ->
  (exists c, c ∈ S1) ->
  binary_alpha_complete itv itv itv interval_add
    (collecting_binary_forward Z.add) i2 i1 S2 S1.
Proof.
  case: i2 => l2 h2; case: i1 => l1 h1.
  apply: (Z_interval_lift2_alpha_complete Z.add).
  - exact: Zadd_monotone_binop.
  - exact: Zadd_order_reflecting_left.
  - exact: Zadd_order_reflecting_right.
  - move=> a b; exists (b - a); lia.
  - move=> a b; exists (b - a); lia.
  - move=> a b; exists (b - a); lia.
  - move=> a b; exists (b - a); lia.
Qed.

End Interval_add.


Section Interval_sub.

  (* This allows reusing the proofs of add + opp. *)
  Local Lemma interval_sub_eq_add_opp i1 i2:
    interval_sub i1 i2 = interval_add i1 (interval_opp i2).
  Proof.
    move: i1 i2 => [[|l1] [|h1]] [[|l2] [|h2]] //=.
  Qed.

  Lemma interval_sub_sound:
    binary_overapproximation itv itv itv interval_sub
      (collecting_binary_forward Z.sub).
  Proof.
    overapproximation_proof. subst c0. rewrite interval_sub_eq_add_opp.
    apply interval_add_sound. exists c2, (-c1). repeat split; try lia.
    - exact Hc2_in_a2.
    - apply interval_opp_exact. exists c1. split; [exact Hc1_in_a1 | lia].
  Qed.

  (** Lift to non-bottom intervals. *)
  Definition nb_interval_sub :=
    non_bottom_lift_total_binary interval_sub Z.sub (Hsound:=interval_sub_sound).

  (** Completeness: every c in γ(sub i2 i1) decomposes as c2 - c1.
      with c2 ∈ γ i2 and c1 ∈ γ i1. We reuse the interval addition
      proof.  *)
  Lemma nb_interval_sub_gamma_complete:
    binary_underapproximation nbitv nbitv nbitv nb_interval_sub
      (collecting_binary_forward Z.sub).
  Proof.
    move=> i2 i1 c0 Hc0.
    (* Rewrite to add + opp form, then decompose via add exactness *)
    rewrite gamma_nbitv_gamma_itv /= interval_sub_eq_add_opp in Hc0.
    have [Hunder _] := nb_interval_add_exact i2 (nb_interval_opp i1).
    have /= := Hunder c0 Hc0.
    unfold_set. move=> [c2 [c_opp [Hc2 [Hcopp Heq]]]].
    (* Witnesses: c2 and -c_opp, since c2 - (-c_opp) = c2 + c_opp = c0 *)
    exists c2, (-c_opp). repeat split; [exact Hc2 | | lia].
    (* -c_opp ∈ γ(i1) follows from c_opp ∈ γ(opp i1) by opp exactness *)
    rewrite gamma_nbitv_gamma_itv /= in Hcopp |- *.
    have [Hopp _] := interval_opp_exact (`i1).
    have := Hopp c_opp Hcopp. unfold_set.
    move=> [c1 [Hc1 Heq1]]. have ->: -c_opp = c1 by lia. exact Hc1.
  Qed.

  Lemma nb_interval_sub_exact:
    binary_exact nbitv nbitv nbitv nb_interval_sub
      (collecting_binary_forward Z.sub).
  Proof.
    move=> i2 i1; split.
    - apply nb_interval_sub_gamma_complete.
    - apply non_bottom_lift_sound.
  Qed.

End Interval_sub.


Require Import Extraction.
Extraction Language OCaml.
Require Import ExtrOcamlBasic.

Extraction Inline non_bottom_lift_total_binary.
(* Extraction Inline ad_car abs_car abstract_domain_to_abstraction. *)
(* Extraction Inline WithTop.lift2. *)

Separate Extraction interval_add nb_interval_add.

