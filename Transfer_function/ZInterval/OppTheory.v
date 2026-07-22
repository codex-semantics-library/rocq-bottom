(* OppTheory.v - [Z.opp] transfer function for the ZInterval single-value
   abstraction: [interval_opp] on one interval. Split out of Z_interval.v.

   Filed on its own rather than with [add]/[sub] because [MulTheory.v] and
   [QuotTheory.v] both reduce sign cases through negation (architecture.org:
   "MulTheory imports OppTheory"). *)

(* STATUS: opp (Z.opp): exact, even when the interval may be bottom
     (interval_opp_sound, interval_opp_exact). *)

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
Require Import Z_interval.
Require Import Transfer_function.ZInterval.OpsComp.
Open Scope Z_scope.
Generalizable All Variables.

(* opp: the unary minus. It is sound and exact, even when the interval may be bottom. *)
Section Interval_opp.

  (** * Negation and best abstraction transfer. *)

  (** Opp is exact, even when the interval is bottom. *)
  Lemma interval_opp_exact:
    unary_exact itv itv interval_opp
      (collecting_forward Z.opp).
  Proof.
    move=> a1. unfold interval_opp.
    have HU:= unfold_set_equiv.
    unfold ExactlyRepresents, collecting_forward; unfold_set.
    move=> c; unfold_set.
    split.
    - move=> H.
      exists (-c); move: a1 H => [[|l] [|h]] H; unfold neg_bound in *;
                           unfold_set in H; unfold_set; simpl in *; lia.
    - move=> [c0 [H1 <-]].
      move: a1 H1 => [[|l] [|h]] H1; unfold_set in *; simpl in *; lia.
  Qed.

  (** Best abstraction transfers through Z.opp:
      if a is best for S, then opp(a) is best for {z | -z ∈ S}. *)
  Lemma best_abstraction_opp (a : interval) (S : propset Z) :
    BestAbstraction (A:=itv) a S ->
    BestAbstraction (A:=itv) (interval_opp a) {[ z | (-z) ∈ S ]}.
  Proof.
    move=> [Hsound Hopt]; apply best_abstraction_iff; split.
    - (* Soundness: (-z) ∈ S ⊆ γ(a), so z ∈ γ(opp(a)) *)
      move=> z; rewrite propset_elem_of_iff => Hz.
      { apply interval_opp_exact. unfold collecting_forward.
        unfold_set. exists (-z).
        split; [by apply Hsound | lia ]. }
    - (* Optimality: opp(b) overapproximates S, so a ⊑ opp(b) *)
      move=> b Hb.
      have Hb': Overapproximates (A:=itv) (interval_opp b) S.
      { move=> z Hz; apply interval_opp_exact. unfold collecting_forward.
        to_set in Hb. unfold_set. exists (-z).
        split.
        + apply Hb; unfold_set. by replace (- -z) with z by lia.
        + lia. }
      move: (Hopt _ Hb') => {Hsound Hopt Hb Hb'}.
      move: a b => [[|la] [|ha]] [[|lb] [|hb]] //=; try lia.
      all: rewrite /GLB.glb_is_included; lia.
  Qed.

  Lemma interval_opp_involutive (i : interval) :
    interval_opp (interval_opp i) = i.
  Proof.
    case: i => [l h] /=; case: l => [|l]; case: h => [|h] //=;
      repeat (f_equal; try lia).
  Qed.

  Lemma propset_opp_involutive (S : ℘ Z) :
    {[ z | -z ∈ {[ z' | -z' ∈ S ]} ]} ⊆⊇ S.
  Proof.
    split=> z; unfold_set => H; by replace (- -z) with z in * by lia.
  Qed.

  (** IsAlpha transports through interval_opp / Z.opp on both sides, since
      opp is an involutive bijection (concrete and abstract) and exact. *)
  Lemma is_alpha_opp_iff (a : interval) (S : ℘ Z) :
    IsAlpha (A:=itv) a S <-> IsAlpha (A:=itv) (interval_opp a) {[ z | -z ∈ S ]}.
  Proof.
    rewrite !is_alpha_iff_best_abstraction. split.
    - exact: best_abstraction_opp.
    - move/best_abstraction_opp. rewrite interval_opp_involutive => Hba.
      exact: (best_abstraction_equiv _ _ _ Hba (propset_opp_involutive _)).
  Qed.

  (** Transport α-completeness across left-argument negation. The new
      abstract function is [fun b2 b1 => interval_opp (fA (interval_opp b2) b1)];
      [fC] is unchanged but must commute with negating its left argument. *)
  Lemma binary_alpha_complete_opp_l
    (fA : interval -> interval -> interval) (fC : setop2 Z Z Z)
    (a2 a1 : interval) (S2 S1 : ℘ Z) :
    (forall T2 T1, fC {[ z | -z ∈ T2 ]} T1 ⊆⊇ {[ z | -z ∈ fC T2 T1 ]}) ->
    binary_alpha_complete itv itv itv fA fC a2 a1 S2 S1 ->
    binary_alpha_complete itv itv itv
      (fun b2 b1 => interval_opp (fA (interval_opp b2) b1)) fC
      (interval_opp a2) a1 {[ z | -z ∈ S2 ]} S1.
  Proof.
    rewrite /binary_alpha_complete => HfC Hac Ha2n Ha1.
    rewrite interval_opp_involutive.
    have Ha2 : IsAlpha (A:=itv) a2 S2.
    { have Hiff := is_alpha_opp_iff (interval_opp a2) {[ z | -z ∈ S2 ]}.
      rewrite interval_opp_involutive in Hiff.
      apply: (is_alpha_set_equiv _ _ _ (propset_opp_involutive S2)).
      exact: (proj1 Hiff Ha2n). }
    have Hres := Hac Ha2 Ha1.
    have Hres' : IsAlpha (A:=itv) (interval_opp (fA a2 a1)) {[ z | -z ∈ fC S2 S1 ]}
      by apply (is_alpha_opp_iff _ _).1.
    apply: (is_alpha_set_equiv _ _ _ _ Hres').
    split; apply HfC.
  Qed.

  (** Right-argument symmetric version. *)
  Lemma binary_alpha_complete_opp_r
    (fA : interval -> interval -> interval) (fC : setop2 Z Z Z)
    (a2 a1 : interval) (S2 S1 : ℘ Z) :
    (forall T2 T1, fC T2 {[ z | -z ∈ T1 ]} ⊆⊇ {[ z | -z ∈ fC T2 T1 ]}) ->
    binary_alpha_complete itv itv itv fA fC a2 a1 S2 S1 ->
    binary_alpha_complete itv itv itv
      (fun b2 b1 => interval_opp (fA b2 (interval_opp b1))) fC
      a2 (interval_opp a1) S2 {[ z | -z ∈ S1 ]}.
  Proof.
    rewrite /binary_alpha_complete => HfC Hac Ha2 Ha1n.
    rewrite interval_opp_involutive.
    have Ha1 : IsAlpha (A:=itv) a1 S1.
    { have Hiff := is_alpha_opp_iff (interval_opp a1) {[ z | -z ∈ S1 ]}.
      rewrite interval_opp_involutive in Hiff.
      apply: (is_alpha_set_equiv _ _ _ (propset_opp_involutive S1)).
      exact: (proj1 Hiff Ha1n). }
    have Hres := Hac Ha2 Ha1.
    have Hres' : IsAlpha (A:=itv) (interval_opp (fA a2 a1)) {[ z | -z ∈ fC S2 S1 ]}
      by apply (is_alpha_opp_iff _ _).1.
    apply: (is_alpha_set_equiv _ _ _ _ Hres').
    split; apply HfC.
  Qed.

  (** opp preserves non-bottom, so we can lift it to nb_interval. *)
  Lemma interval_opp_preserves_non_bottom i:
    non_bottom i -> non_bottom (interval_opp i).
  Proof. move: i => [[|l] [|h]] //=; lia. Qed.

  Definition nb_interval_opp (i : nb_interval) : nb_interval :=
    exist _ (interval_opp (`i)) (interval_opp_preserves_non_bottom _ (proj2_sig i)).

End Interval_opp.
