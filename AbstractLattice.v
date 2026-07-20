Require Import Abstraction.
Require Import ssreflect.

(** * AbstractLattice: Abstractions with join semilattice and lattice operations. *)

(** ** Abstract Join Semilattice.

    An abstract join semilattice extends an abstract domain with a
    computable join operation and equivalence. This is the minimal
    structure needed for domains like congruence or known-bits-without-bottom
    that have join but no meaningful meet.

    Note: as we have some properties, like StrongAlphaRelation, that
    explicitly depend on an abstract domain, we require and reuse that
    same abstract domain. *)

Class abstract_join_semilattice_laws {C: Type} (A: abstract_domain C)
  (join: A -> A -> A) (equiv: A -> A -> Prop) := {
    ajsl_ad_laws :> abstract_domain_laws (γ[A] ) (⊑[A]);
    (* Equiv is an equivalence relation which is stronger than ⊑⊒,
       but may be different (we have no example of this for now). *)
    ajsl_equiv_compat: forall a1 a2, equiv a1 a2 -> a1 ⊑[A] a2 /\ a2 ⊑[A] a1;

    (* Note: From a soundness point of view, we just want the join
       operation to return an over-approximation of the union, i.e. to
       be compatible with the concrete order. Compatibility with the
       abstract order is more strict, but it seems to be a reasonable
       assumption. *)
    ajsl_join_compat_l: forall a1 a2, a1 ⊑[A] (join a1 a2);
    ajsl_join_compat_r: forall a1 a2, a2 ⊑[A] (join a1 a2);
  }.

Structure abstract_join_semilattice (C:Type) :=
  BuildAbstractJoinSemilattice {
      ajsl_ad :> abstract_domain C;
      ajsl_join: ajsl_ad -> ajsl_ad -> ajsl_ad;
      ajsl_equiv: ajsl_ad -> ajsl_ad -> Prop;
      ajsl_mixin: @abstract_join_semilattice_laws C ajsl_ad ajsl_join ajsl_equiv
    }.
Arguments BuildAbstractJoinSemilattice {_} _ _ _ _.
Arguments ajsl_ad {_} _ /.
Arguments ajsl_join {_} _.
Arguments ajsl_equiv {_} _.
Arguments ajsl_mixin {_} _ /.
Existing Instance ajsl_mixin.

(** Notations for join semilattice operations *)
Global Notation "(⊔[ A ])" := (@ajsl_join _ A).
Global Notation "a1 ⊔[ A ] a2" := (@ajsl_join _ A a1 a2) (at level 50, left associativity).
Global Notation "(≡[ A ])" := (@ajsl_equiv _ A).
Global Notation "a1 ≡[ A ] a2" := (@ajsl_equiv _ A a1 a2) (at level 70).

(** Coercion from abstract_join_semilattice to abstract_domain. *)
Definition abstract_join_semilattice_to_abstract_domain {C} (AJSL: abstract_join_semilattice C) : abstract_domain C := ajsl_ad AJSL.
Global Coercion abstract_join_semilattice_to_abstract_domain : abstract_join_semilattice >-> abstract_domain.
Global Arguments abstract_join_semilattice_to_abstract_domain {_} _ /.
Global Hint Unfold abstract_join_semilattice_to_abstract_domain: unfold_gamma.

(** ** Abstract Lattice.

    An abstract lattice extends an abstract join semilattice with a
    meet operation. Note that there are currently no laws on meet
    (soundness of meet is not required at this level). *)

Structure abstract_lattice (C:Type) :=
  MkAbstractLattice {
      al_ajsl :> abstract_join_semilattice C;
      al_meet: al_ajsl -> al_ajsl -> al_ajsl;
    }.
Arguments MkAbstractLattice {_} _ _.
Arguments al_ajsl {_} _ /.
Arguments al_meet {_} _.

(** Backward-compatible constructor: same argument order as the old
    BuildAbstractLattice, except the laws type no longer mentions meet. *)
Definition BuildAbstractLattice {C} (ad: abstract_domain C)
  (join: ad -> ad -> ad) (meet: ad -> ad -> ad)
  (equiv: ad -> ad -> Prop)
  (laws: @abstract_join_semilattice_laws C ad join equiv)
  : abstract_lattice C :=
  MkAbstractLattice (BuildAbstractJoinSemilattice ad join equiv laws) meet.

(** Notation for meet (stays on abstract_lattice) *)
Global Notation "(⊓[ A ])" := (@al_meet _ A).
Global Notation "a1 ⊓[ A ] a2" := (@al_meet _ A a1 a2) (at level 50, left associativity).

(** Coercion from abstract_lattice to abstract_domain (direct path
    for robustness, in addition to the chain via abstract_join_semilattice). *)
Definition abstract_lattice_to_abstract_domain {C} (AL: abstract_lattice C) : abstract_domain C := ajsl_ad (al_ajsl AL).
Global Coercion abstract_lattice_to_abstract_domain : abstract_lattice >-> abstract_domain.
Global Arguments abstract_lattice_to_abstract_domain {_} _ /.
Global Hint Unfold abstract_lattice_to_abstract_domain: unfold_gamma.

(** Backward-compatible accessors *)
Definition al_ad {C} (AL: abstract_lattice C) : abstract_domain C := ajsl_ad (al_ajsl AL).
Definition al_join {C} (AL: abstract_lattice C) := ajsl_join (al_ajsl AL).
Definition al_equiv {C} (AL: abstract_lattice C) := ajsl_equiv (al_ajsl AL).

(** ** Join Semilattice Theorems.

    All the following theorems only depend on the join semilattice
    structure, not on meet. *)

(** Join semilattice laws imply soundness of join. *)
Theorem join_sound {C:Type} (AJSL:abstract_join_semilattice C) :
  forall a1 a2, (γ[AJSL] a1 ∪ γ[AJSL] a2) ⊆ γ[AJSL] (a1 ⊔[AJSL] a2).
Proof.
  move=> a1 a2.
  assert (H1: γ[AJSL] a1 ⊆ γ[AJSL] (a1 ⊔[AJSL] a2)).
  { apply ad_γ_order_preserving. apply ajsl_join_compat_l.  }
  assert (H2: γ[AJSL] a2 ⊆ γ[AJSL] (a1 ⊔[AJSL] a2)).
  { apply ad_γ_order_preserving. apply ajsl_join_compat_r.  }
  unfold_set in *; firstorder.
Qed.


(** Join is a true LUB (optional property of abstract_join_semilattice). *)
Class JoinIsLUB {C: Type} (AJSL: abstract_join_semilattice C) :=
  join_lub: forall (a1 a2 c : AJSL),
      a1 ⊑[AJSL] c -> a2 ⊑[AJSL] c -> (a1 ⊔[AJSL] a2) ⊑[AJSL] c.

(** Many classic lattice properties come when join is a LUB; but we
replace equality by the (⊑⊒[AJSL]) equivalence relation. *)
Theorem join_associative {C:Type} (AJSL:abstract_join_semilattice C) :
  @JoinIsLUB C AJSL -> (forall a1 a2 a3, a1 ⊔[AJSL] (a2 ⊔[AJSL] a3) ⊑⊒[AJSL] (a1 ⊔[AJSL] a2) ⊔[AJSL] a3).
Proof.
  move => HLUB a1 a2 a3.
  split.
  - apply: join_lub.
    + transitivity (a1 ⊔[ AJSL] a2). apply ajsl_join_compat_l. apply ajsl_join_compat_l.
    + apply: join_lub.
      * transitivity (a1 ⊔[ AJSL] a2). apply ajsl_join_compat_r. apply ajsl_join_compat_l.
      * apply ajsl_join_compat_r.
  - apply: join_lub.
    + apply: join_lub.
      * apply: ajsl_join_compat_l.
      * transitivity (a2 ⊔[ AJSL] a3). apply ajsl_join_compat_l. apply ajsl_join_compat_r.
    + transitivity (a2 ⊔[ AJSL] a3). apply ajsl_join_compat_r. apply ajsl_join_compat_r.
Qed.

Theorem join_commutative {C:Type} (AJSL:abstract_join_semilattice C) :
  @JoinIsLUB C AJSL -> forall a1 a2, (a1 ⊔[AJSL] a2) ⊑⊒[AJSL] (a2 ⊔[AJSL] a1).
Proof.
  move => HLUB a1 a2.
  split.
  - apply: join_lub. apply: ajsl_join_compat_r. apply: ajsl_join_compat_l.
  - apply: join_lub. apply: ajsl_join_compat_r. apply: ajsl_join_compat_l.
Qed.

Theorem join_idempotent {C:Type} (AJSL:abstract_join_semilattice C) :
  @JoinIsLUB C AJSL -> forall a, (a ⊔[AJSL] a) ⊑⊒[AJSL] a.
Proof.
  move => HLUB a.
  split.
  - apply: join_lub; reflexivity.
  - apply: ajsl_join_compat_l.
Qed.

Instance JoinProper {C:Type} (AJSL:abstract_join_semilattice C) `{JoinIsLUB C AJSL}:
  Proper ((⊑⊒[ AJSL ]) ==> (⊑⊒[ AJSL ]) ==> (⊑⊒[ AJSL ])) (⊔[AJSL]).
Proof.
  move => a1 a2 [H12 H21] a3 a4 [H34 H43].
  split.
  - apply: join_lub.
    + transitivity a2.
      * assumption.
      * apply: ajsl_join_compat_l.
    + transitivity a4.
      * assumption.
      * apply: ajsl_join_compat_r.
  - apply: join_lub.
    + transitivity a1.
      * assumption.
      * apply: ajsl_join_compat_l.
    + transitivity a3.
      * assumption.
      * apply: ajsl_join_compat_r.
Qed.

(** This is the "connecting lemma" from lattices as ordered sets to
    lattices as algebraic structures.  *)
Theorem sqsubseteq_is_join_equiv {C:Type} (AJSL:abstract_join_semilattice C) :
  @JoinIsLUB C AJSL -> (forall a1 a2, a1 ⊑[AJSL] a2 <-> (a1 ⊔[AJSL] a2) ⊑⊒[ AJSL ] a2).
Proof.
  move=> HLUB a1 a2. split.
  -  move => H1le2. split.
     + apply: HLUB. exact H1le2. reflexivity.
     + apply: ajsl_join_compat_r.
  - move => [H1 H2].
    transitivity (a1 ⊔[ AJSL] a2).
    + apply ajsl_join_compat_l.
    + exact H1.
Qed.

(** This is the connecting lemma from lattices as algebraic structures
to lattices as ordered sets. Maybe useful when equivalence is simple
(e.g., equality).  *)
Theorem sqsubseteq_is_join_equiv_implies_lub {C:Type} (AJSL:abstract_join_semilattice C)
  (Hassoc: forall a1 a2 a3, ((a1 ⊔[AJSL] a2) ⊔[AJSL] a3)  ⊑⊒[AJSL]  (a1 ⊔[AJSL] (a2 ⊔[AJSL] a3)))
  (JoinProper:Proper ((⊑⊒[ AJSL ]) ==> (⊑⊒[ AJSL ]) ==> (⊑⊒[ AJSL ])) (⊔[AJSL])) :
  (forall a1 a2, a1 ⊑[AJSL] a2 <-> (a1 ⊔[AJSL] a2) ⊑⊒[ AJSL ] a2) -> @JoinIsLUB C AJSL.
Proof.
  assert(Equivalence (⊑⊒[ AJSL ])) by apply _.
  move => H_equiv a1 a2 c /H_equiv Ha1lec /H_equiv Ha2lec.
  apply /H_equiv.
  transitivity (a1 ⊔[AJSL] (a2 ⊔[AJSL] c)).
  - apply Hassoc.
  - setoid_rewrite Ha2lec. exact Ha1lec.
Qed.


(** Best abstraction distributes over union when join is a true LUB.
    This allows for reasoning by case for best-abstraction proofs
    (e.g., for interval multiplication).

    Remark that (a1 ⊔ a2) is the best abstraction of (S1 ∪ S2) only if
    a1 and a2 are the best abstractions of resp S1 and S2; i.e. (a1 ⊔
    a2) may not be the best abstraction of the union
    operation. Furthermore, passing to ⊔ some abstractions that are
    not the best abstraction may lead to precision losses in the
    concrete.

    Consider for instance, ([5,15],multiple of 10) ⊔ ([8,12],multiple
    of 5) = ([5,15],multiple of 5), whose concretization is
    \{5;10;15\}, while each of argument concretizes to \{10\}. This is
    why one should always perform a maximal reduction before passing
    the arguments to join, as in that case, the join is guaranteed to
    return the best abstraction of the union.

    TODO: this states that the join is α-complete. The converse (i.e., that
    α-completeness of the join implies [JoinIsLUB]) is plausible, but has not
    been verified. *)
Lemma is_alpha_join {C} (AJSL: abstract_join_semilattice C) `{!JoinIsLUB AJSL}
  (a1 a2: AJSL) (S1 S2: propset C) :
  IsAlpha (A:=AJSL) a1 S1 -> IsAlpha (A:=AJSL) a2 S2 ->
  IsAlpha (A:=AJSL) (a1 ⊔[ AJSL] a2) (S1 ∪ S2).
Proof.
  set ll := ajsl_mixin AJSL.
  move => Hadj1 Hadj2 a. split.
  - move => Hsub. apply join_lub.
    + apply Hadj1. move=> z Hz. apply Hsub. unfold_set. left. exact Hz.
    + apply Hadj2. move=> z Hz. apply Hsub. unfold_set. right. exact Hz.
  - move=> Hle z Hz.
    assert (Ha1: a1 ⊑[AJSL] a).
    { transitivity (a1 ⊔[ AJSL] a2). apply ajsl_join_compat_l. exact Hle. }
    assert (Ha2: a2 ⊑[AJSL] a).
    { transitivity (a1 ⊔[ AJSL] a2). apply ajsl_join_compat_r. exact Hle. }
    apply Hadj1 in Ha1.
    apply Hadj2 in Ha2.
    destruct Hz; [by apply Ha1|by apply Ha2].
Qed.

(** Generic split: if [S] decomposes as a union of two parts [S_a] and
    [S_b] each best-abstracted by [a_a] and [a_b], then [a_a ⊔ a_b] is
    α for [S]. Pure composition of [is_alpha_join] and
    [IsAlpha_set_equiv]; lifts to richer join-semilattices (e.g.
    reduced products with congruence) where the join can capture
    structure the interval domain cannot. *)
Lemma is_alpha_join_split {C} (AJSL: abstract_join_semilattice C) `{!JoinIsLUB AJSL}
  (a_a a_b : AJSL) (S S_a S_b : propset C) :
  S ⊆⊇ S_a ∪ S_b ->
  IsAlpha (A:=AJSL) a_a S_a -> IsAlpha (A:=AJSL) a_b S_b ->
  IsAlpha (A:=AJSL) (a_a ⊔[ AJSL] a_b) S.
Proof.
  move=> [Hsub Hsup] Ha Hb.
  apply: (is_alpha_set_equiv _ (S_a ∪ S_b) S _ (is_alpha_join _ _ _ _ _ Ha Hb)).
  by split.
Qed.

(** A corollary is that the result of join is maximally reduced: apply
    with S1 = (γ[AJSL] a1), + the fact that join is the best
    abstraction of the union when the arguments are best. *)
Corollary join_is_lub_maximally_reduced {C} (AJSL: abstract_join_semilattice C) `{JUL:!JoinIsLUB AJSL}
  a1 a2 :
  IsAlpha a1 (γ[AJSL] a1) -> IsAlpha a2 (γ[AJSL] a2) ->
  let a := (a1 ⊔[AJSL] a2) in IsAlpha a (γ[AJSL] a).
Proof.
  move=> H1 H2 a.
  have H: IsAlpha a ((γ[AJSL] a1) ∪ (γ[AJSL] a2)) by apply: is_alpha_join.
  clear H1 H2.
  rewrite is_alpha_iff_best_abstraction. rewrite is_alpha_iff_best_abstraction in H.
  split.
  - done. (* Overapproximate: trivial. *)
  - move=> a' Ha'. apply H. to_set in *. transitivity ((γ[ AJSL] ) a).
    + exact: join_sound.
    + exact: Ha'.
Qed.

(** Two-function binary wrappers around [is_alpha_join_split] for
    [binary_alpha_complete]. The two halves may be abstracted by
    *different* transfer functions [fA_a] / [fA_b] — exactly the shape of
    the across-zero [interval_mul] cases, where one half goes through the
    [Neg] quadrant transfer and the other through the [Pos] one. (The
    single-function form is the special case [fA_a = fA_b].) The result
    domain [A0] must be a join-semilattice (the other argument may stay in
    a plain [abstract_domain]). The [fC] distributivity hypothesis is
    discharged at call sites via [collecting_binary_forward_union_l] /
    [collecting_binary_forward_union_r] (Abstraction.v).

    [_l] splits the left ([a2]) operand's set, [_r] the right ([a1]) one. *)
Lemma binary_alpha_complete_split_l
  {C2 C1 C0 : Type} (A2: abstract_domain C2) (A1: abstract_domain C1)
  (A0: abstract_join_semilattice C0) `{!JoinIsLUB A0}
  (fA_a fA_b : A2 -> A1 -> A0) (fC : setop2 C2 C1 C0)
  (a2_a a2_b : A2) (a1 : A1)
  (S2 S2_a S2_b : propset C2) (S1 : propset C1) :
  (forall T1, fC S2 T1 ⊆⊇ fC S2_a T1 ∪ fC S2_b T1) ->
  IsAlpha (A:=A2) a2_a S2_a -> IsAlpha (A:=A2) a2_b S2_b ->
  binary_alpha_complete A2 A1 A0 fA_a fC a2_a a1 S2_a S1 ->
  binary_alpha_complete A2 A1 A0 fA_b fC a2_b a1 S2_b S1 ->
  IsAlpha (A:=A1) a1 S1 ->
  IsAlpha (A:=A0) (fA_a a2_a a1 ⊔[A0] fA_b a2_b a1) (fC S2 S1).
Proof.
  move=> HfC Ha2a Ha2b Hac_a Hac_b Ha1.
  have Hα_a := Hac_a Ha2a Ha1.
  have Hα_b := Hac_b Ha2b Ha1.
  exact: (is_alpha_join_split _ _ _ _ _ _ (HfC S1) Hα_a Hα_b).
Qed.

Lemma binary_alpha_complete_split_r
  {C2 C1 C0 : Type} (A2: abstract_domain C2) (A1: abstract_domain C1)
  (A0: abstract_join_semilattice C0) `{!JoinIsLUB A0}
  (fA_a fA_b : A2 -> A1 -> A0) (fC : setop2 C2 C1 C0)
  (a2 : A2) (a1_a a1_b : A1)
  (S2 : propset C2) (S1 S1_a S1_b : propset C1) :
  (forall T2, fC T2 S1 ⊆⊇ fC T2 S1_a ∪ fC T2 S1_b) ->
  IsAlpha (A:=A1) a1_a S1_a -> IsAlpha (A:=A1) a1_b S1_b ->
  binary_alpha_complete A2 A1 A0 fA_a fC a2 a1_a S2 S1_a ->
  binary_alpha_complete A2 A1 A0 fA_b fC a2 a1_b S2 S1_b ->
  IsAlpha (A:=A2) a2 S2 ->
  IsAlpha (A:=A0) (fA_a a2 a1_a ⊔[A0] fA_b a2 a1_b) (fC S2 S1).
Proof.
  move=> HfC Ha1a Ha1b Hac_a Hac_b Ha2.
  have Hα_a := Hac_a Ha2 Ha1a.
  have Hα_b := Hac_b Ha2 Ha1b.
  exact: (is_alpha_join_split _ _ _ _ _ _ (HfC S2) Hα_a Hα_b).
Qed.

(** ** Module Types *)

Module Type ABSTRACT_JOIN_SEMILATTICE.
  Include ABSTRACT_DOMAIN.

  Parameter equal: t -> t -> bool.
  Parameter join: t -> t -> t.
End ABSTRACT_JOIN_SEMILATTICE.

(* A lattice representing a set of values. *)
Module Type ABSTRACT_LATTICE.
  Include ABSTRACT_JOIN_SEMILATTICE.

  Parameter meet: t -> t -> t.
  (* Optional components: bottom, is_bottom, top, is_top.
     We don't require them for intermediate lattices. *)

End ABSTRACT_LATTICE.
