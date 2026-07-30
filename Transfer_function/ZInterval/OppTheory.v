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
Require Import ZInterval.
Require Import ZIntervalTheory.
Require Import Transfer_function.ZInterval.ZIntervalOps.
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

  (** Map a set equivalence through [Z.opp]. *)
  Lemma propset_opp_equiv (S S' : ℘ Z) : S ⊆⊇ S' -> {[z | -z ∈ S]} ⊆⊇ {[z | -z ∈ S']}.
  Proof.
    move=> [H H']. split => z Hz; unfold_set in Hz; unfold_set.
    - exact: (H _ Hz).
    - exact: (H' _ Hz).
  Qed.

  (** Solving an equivalence for the negated side: an operation that commutes
      with negation states its commutation as [f (-S) ⊆⊇ -(f S)], but what the
      sign-case transports consume is that read the other way round.  Negate
      both sides and cancel — this one propset rule is the whole content of the
      per-operation [collecting_*_opp_{l,r}_inv] lemmas it replaces, and it
      composes by [transitivity] like any other rewriting step. *)
  Lemma propset_opp_equiv_inv (S S' : ℘ Z) :
    S ⊆⊇ {[ z | -z ∈ S' ]} -> {[ z | -z ∈ S ]} ⊆⊇ S'.
  Proof.
    move=> H. transitivity {[ z | -z ∈ {[ z' | -z' ∈ S' ]} ]}.
    - exact: propset_opp_equiv.
    - exact: propset_opp_involutive.
  Qed.

  (** Non-emptiness transports through [Z.opp], for the existence hypotheses of
      the quarter transports. *)
  Lemma opp_nonempty (S : ℘ Z) : (exists c, c ∈ S) -> exists c, c ∈ {[ z | -z ∈ S ]}.
  Proof. move=> [c Hc]. exists (-c). by unfold_set; replace (- - c) with c by lia. Qed.

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

  (** opp preserves non-bottom, so we can lift it to nb_interval. *)
  Lemma interval_opp_preserves_non_bottom i:
    non_bottom i -> non_bottom (interval_opp i).
  Proof. move: i => [[|l] [|h]] //=; lia. Qed.

  Definition nb_interval_opp (i : nb_interval) : nb_interval :=
    exist _ (interval_opp (`i)) (interval_opp_preserves_non_bottom _ (proj2_sig i)).

End Interval_opp.
