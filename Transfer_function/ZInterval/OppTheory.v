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

  (** The bound-level involution. *)
  Lemma bound_opp_involutive (a : WithTop.with_top Z) : bound_opp (bound_opp a) = a.
  Proof. by case: a => [|a] //=; rewrite Z.opp_involutive. Qed.

  Lemma interval_opp_involutive (i : interval) :
    interval_opp (interval_opp i) = i.
  Proof.
    case: i => [l h] /=. by repeat rewrite -> bound_opp_involutive.
  Qed.

  (** Soundness: [opp] of a point of the input interval lands in the output
      interval, by antitonicity of [Z.opp]. *)
  Lemma interval_opp_sound :
    unary_overapproximation itv itv interval_opp (collecting_forward Z.opp).
  Proof.
    move=> a c. unfold_set. move=> [c0 [Hc0 <-]].
    move: a Hc0 => [[|l] [|h]] /=; unfold_set => Hc0; unfold_set; split => //=.
    all: lia.
  Qed.

  (** Opp is sound and and involution in the abstract, so exact. *)
  Lemma interval_opp_exact:
    unary_exact itv itv interval_opp
      (collecting_forward Z.opp).
  Proof.
    apply: (sound_involutive_exact itv Z.opp interval_opp
              Z.opp_involutive interval_opp_involutive interval_opp_sound).
  Qed.

  (** [interval_opp] preserves ⊑.  Raw [itv] has no [ExactOrder], so this
      has to be checked on the bounds. *)
  Lemma interval_opp_monotone (a b : interval) :
    a ⊑[itv] b -> interval_opp a ⊑[itv] interval_opp b.
  Proof.
    move: a b => [[|la] [|ha]] [[|lb] [|hb]] //=; try lia.
    all: rewrite /GLB.glb_is_included; lia.
  Qed.

  (** The rest of this section is [Section AbstractBijection] instantiated
      at [Z.opp] / [interval_opp], each its own inverse.  The names and
      statements are unchanged; only the proofs are now shared with
      [Z.lnot] and with the translation [c ↦ c + K]. *)

  (** Best abstraction transfers through Z.opp:
      if a is best for S, then opp(a) is best for {z | -z ∈ S}. *)
  Lemma best_abstraction_opp (a : interval) (S : propset Z) :
    BestAbstraction (A:=itv) a S ->
    BestAbstraction (A:=itv) (interval_opp a) {[ z | (-z) ∈ S ]}.
  Proof.
    exact: (best_abstraction_bijection itv Z.opp Z.opp interval_opp interval_opp
              Z.opp_involutive Z.opp_involutive
              interval_opp_involutive interval_opp_involutive
              interval_opp_monotone interval_opp_monotone
              interval_opp_sound interval_opp_sound a S).
  Qed.

  Lemma propset_opp_involutive (S : ℘ Z) :
    {[ z | -z ∈ {[ z' | -z' ∈ S ]} ]} ⊆⊇ S.
  Proof.
    exact: (propset_preimage_cancel Z.opp Z.opp Z.opp_involutive S).
  Qed.

  (** Map a set equivalence through [Z.opp]. *)
  Lemma propset_opp_equiv (S S' : ℘ Z) : S ⊆⊇ S' -> {[z | -z ∈ S]} ⊆⊇ {[z | -z ∈ S']}.
  Proof. exact: (propset_preimage_equiv Z.opp S S'). Qed.

  (** Solving an equivalence for the negated side: an operation that commutes
      with negation states its commutation as [f (-S) ⊆⊇ -(f S)], but what the
      sign-case transports consume is that read the other way round.  Negate
      both sides and cancel — this one propset rule is the whole content of the
      per-operation [collecting_*_opp_{l,r}_inv] lemmas it replaces, and it
      composes by [transitivity] like any other rewriting step. *)
  Lemma propset_opp_equiv_inv (S S' : ℘ Z) :
    S ⊆⊇ {[ z | -z ∈ S' ]} -> {[ z | -z ∈ S ]} ⊆⊇ S'.
  Proof.
    exact: (propset_preimage_equiv_inv Z.opp Z.opp Z.opp_involutive S S').
  Qed.

  (** Non-emptiness transports through [Z.opp], for the existence hypotheses of
      the quarter transports. *)
  Lemma opp_nonempty (S : ℘ Z) : (exists c, c ∈ S) -> exists c, c ∈ {[ z | -z ∈ S ]}.
  Proof. exact: (preimage_nonempty Z.opp Z.opp Z.opp_involutive S). Qed.

  (** IsAlpha transports through interval_opp / Z.opp on both sides, since
      opp is an involutive bijection (concrete and abstract) and exact. *)
  Lemma is_alpha_opp_iff (a : interval) (S : ℘ Z) :
    IsAlpha (A:=itv) a S <-> IsAlpha (A:=itv) (interval_opp a) {[ z | -z ∈ S ]}.
  Proof.
    exact: (is_alpha_bijection_iff itv Z.opp Z.opp interval_opp interval_opp
              Z.opp_involutive Z.opp_involutive
              interval_opp_involutive interval_opp_involutive
              interval_opp_monotone interval_opp_monotone
              interval_opp_sound interval_opp_sound a S).
  Qed.

  (** α-completeness in [collecting_forward] form.  [Z.lnot] had this and
      [Z.opp] did not; the generic section gives both. *)
  Lemma interval_opp_alpha_complete (a : interval) (S : ℘ Z) :
    unary_alpha_complete itv itv interval_opp (collecting_forward Z.opp) a S.
  Proof.
    exact: (bijection_alpha_complete itv Z.opp Z.opp interval_opp interval_opp
              Z.opp_involutive Z.opp_involutive
              interval_opp_involutive interval_opp_involutive
              interval_opp_monotone interval_opp_monotone
              interval_opp_sound interval_opp_sound a S).
  Qed.

  (** Negating a sign-definite interval flips its type.  Only the proofs need
      this: in [ZIntervalOps.v] the [Program] coercion builds it inline. *)
  Program Definition opp_neg_pos (i : neg_interval) : pos_interval :=
    interval_opp i.
  Next Obligation.
    move: i => [[[|l] [|h]] [Hnb Hh]] //=; simpl in Hnb, Hh; split=> //; lia.
  Qed.

  (** opp preserves non-bottom, so we can lift it to nb_interval. *)
  Lemma interval_opp_preserves_non_bottom i:
    non_bottom i -> non_bottom (interval_opp i).
  Proof. move: i => [[|l] [|h]] //=; lia. Qed.

  Program Definition nb_interval_opp (i : nb_interval) : nb_interval := interval_opp i.
  Next Obligation.
    move: i => [i Hnb]. simpl. by apply interval_opp_preserves_non_bottom.
  Defined.

End Interval_opp.
