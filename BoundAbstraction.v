Require Import Corelib.Classes.CRelationClasses.
Require Import Stdlib.ZArith.ZArith.
Require Import Abstraction AbstractLattice.
Require Import AbstractionCombination.
Require Import ssreflect ssrbool ssrfun.
Require Import autoreflect.
Generalizable All Variables.

(** * GLB. *)

(** Whenever we have a preorder, we can define an Abstraction where we
    use an element to represent (via γ) the set of all the larger
    elements. We can define α as the greatest lowest bound of this set
    (but it does not always exists, e.g. when abtracting π using
    rationals. *)
Module GLB. Section GLB.

  Context {A : Type} (le : relation A) {Hpre : PreOrder le}.
  Local Notation "(≤)" := le (only parsing).
  Local Infix "≤" := le (at level 70).

  (** γ contains everything 'above' the bound according to the preorder.
      Conversely, a set is abstracted by its greatest lower bound. *)
  Definition γ_glb := fun a => {[ c | a ≤ c ]}.

  (** We define a1 ⊑ a2 <-> le a2 a1 (note the inversion). Indeed,
      if 7 <= 8, then 8 is a more precise lowerbound than 7. *)  
  Definition glb_is_included (a1 a2 : A) : Prop := a2 ≤ a1.

  Definition abs: abstraction A := BuildAbstraction γ_glb.
  
  Program Instance glb_laws: abstract_domain_laws (A:=abs) γ_glb glb_is_included.
  Next Obligation.              (* PreOrder. *)
    by apply flip_PreOrder.
  Qed.
  Next Obligation.              (* OrderPreserving. *)
    (* a1 ⊑ a2 => a1 ⊑γ a2 *)
    to_set.
    move=> a1 a2 H_a1_le_a2. rewrite /Abstraction.γ/γ_glb.
    repeat unfold_set.  rewrite /glb_is_included in H_a1_le_a2.
    move=> c Hc_in_a1. by transitivity a1.
  Qed.
  
  Definition ad : abstract_domain A := BuildAbstractDomain γ_glb glb_is_included glb_laws.

  (** A strong property of the bound abstraction: the abstract and
      concrete orders correspond. This will still be true when
      extended to top, to intervals, and when we distinguish open and
      close bounds. *)
  Instance glb_is_included_exact : ExactOrder ad.
  Proof using Hpre.
    move=> a1 a2. to_set; split.
    - exact: (ad_sqsubseteq_order_preserving ad).
    - move/(_ a1) => H. apply: H. unfold_set. reflexivity.
  Qed.

  (** We have a Galois connection for the lowerbound abstraction, and
      α(S) is the greatest lower bound of S.

      Remember that the greatest lowest bound does not always exists;
      e.g. the {q ∈ Q | q^2 < 2} is bounded but does not have a
      glb. However, if it exists, it corresponds to alpha. *)
  Record is_glb (bound : A) (S : propset A) : Prop :=  {
      glb_is_lowerboud: (forall z, z ∈ S -> bound ≤ z);
      glb_is_greatest: (forall z, (forall y, y ∈ S -> z ≤ y) -> z ≤ bound)
    }.

  Program Instance galois : StrongAlphaRelation ad :=
    {| strong_α_relation := fun (a:ad) (S:propset A) => is_glb a S |}.
  Next Obligation.
    (* The glb looks a lot like our definition of most precise.
       We swap this with the Adjunction; we can because the abstract
        order is exact. *)   
    rewrite -(most_precise_is_is_alpha (A:=ad)).

    (* glb_is_greatest is almost like Upperboundinprecision, save from
    this equivalence. *)
    assert(H: forall z x, z ≤ x <-> forall y : A, x ≤ y -> z ≤ y).
    { split.
      - move => H y Hy. by transitivity x.
      - move => H. apply: H. reflexivity.
    }
    split.
    - (* is_glb -> MostPrecise. *)
      move=> [glb_is_lowerbound glb_is_greatest]. split.
      + exact glb_is_lowerbound.
      + to_set; unfold_gamma; repeat simpl. unfold_set. move=> z.
        rewrite -H. exact: glb_is_greatest.
    - (* MostPrecise -> is_glb. *)
      move=> [HOvapproximate HUpperBoundInPrecision].
      split.
      + (* glb_is_lowerboud. *) exact HOvapproximate.
      + (* glb is greated bound. *)
        move=> z Hz_lb. (* If z is a lower bound: prove z <= a. *)
        rewrite H. exact: HUpperBoundInPrecision.
  Qed.

  Global Instance is_includedP leb a1 a2:
    (AutoReflect(a2 ≤ a1)(leb a2 a1)) ->
    (AutoReflect(a1 ⊑[ad] a2)(leb a2 a1)).
  Proof. done. Qed.
    
(* If the le relation is antisymmetric, then γ for the glb is
  injective.  *) (* Instance glb_injective `{E:Equiv A}
  `{Hanti:Antisymmetric A E le} `{!@HasEquiv A A γ_glb E} :
  IsGammaInjective glb. *) (* Proof using Hpre. *) (* intros x y
  Hgamma_eq. *) (* set_unfold in Hgamma_eq.  *) (* apply Hanti. *) (*
  all: apply Hgamma_eq; reflexivity. *) (* Qed. *)
  (** γ[GLB] is upward-closed: if c1 is above the bound, so is any c2 ≥ c1. *)
  Lemma gamma_upward (b : A) (c1 c2 : A) :
    c1 ∈ γ[ad] b -> c1 ≤ c2 -> c2 ∈ γ[ad] b.
  Proof using Hpre. simpl; unfold_set. move=> Hb Hc. by transitivity c1. Qed.

End GLB. End GLB.
Global Hint Unfold GLB.γ_glb : unfold_gamma.

(** * LUB. *)

Module LUB. Section LUB.

  Context {A : Type} (le : relation A) {Hpre : PreOrder le}.
  Local Notation "(≤)" := le (only parsing).
  Local Infix "≤" := le (at level 70).

  Local Notation "(≥)" := (flip le) (only parsing).
  Local Infix "≥" := (flip le) (at level 70).

  Local Instance FlipPreOrder : PreOrder (≥).
  Proof using Hpre. by apply: flip_PreOrder. Qed.
  Local Definition glb_flip : abstract_domain A := GLB.ad (≥). 

  (** The lub concretize into the set of elements that are smaller. *)         
  Definition γ_lub := fun (a:A) => {[ z | z ≤ a ]}.
  Definition lub_is_included := (≤).

  Definition abs: abstraction A := BuildAbstraction γ_lub.

  Program Instance lub_laws: abstract_domain_laws (A:=abs) γ_lub lub_is_included.
  Next Obligation.
    hnf. firstorder.
  Qed.
  
  Definition ad : abstract_domain A := BuildAbstractDomain γ_lub (≤) lub_laws.
  
  Definition sqsubseteq_lub_is_sqsubseteq_glb_flip:
    forall a1 a2, a1 ⊑[ad] a2 <-> a1 ⊑[glb_flip] a2.
  Proof. reflexivity. Qed.

  Definition gamma_lub_is_gamma_glb_flip:
    forall a, γ[ad] a ⊆⊇ γ[glb_flip] a.
  Proof. reflexivity. Qed.

  Instance lub_is_included_exact : ExactOrder ad.
  Proof.
    have H: ExactOrder glb_flip by apply GLB.glb_is_included_exact.
    exact H.
  Qed.

  Record is_lub (bound : A) (S : propset A) : Prop := {
      lub_is_upperbound: (forall z, z ∈ S -> le z bound);
      lub_is_lowest: (forall z', (forall y, y ∈ S -> y ≤ z') -> bound ≤ z')
    }.

  (* The lub is also a galois connection; we reuse the glb proof. *)
  Program Instance galois : StrongAlphaRelation ad :=
    { strong_α_relation := is_lub }.
  Next Obligation.
    pose (H:=GLB.galois (≥)).
    have H2: a ≡α[glb_flip] S <-> (@IsAlpha A glb_flip a S) by apply (strong_α_relation_spec (StrongAlphaRelation:=H)).
    firstorder.
  Qed.
  
  (** If the le relation is antisymmetric, then γ for the lub is
  injectiv.  *) (* Instance lub_injective {A} le `{Hpre:PreOrder A le} *)
                (*   `{E:Equiv A} `{Hanti:Antisymmetric A E le} `{!@HasEquiv A A (γ_lub *)
                (*                                                                  le) E} : IsGammaInjective (γ_lub le).  Proof.  intros x y Hgamma_eq. *)
                (*                                                                                                                 set_unfold in Hgamma_eq.  apply Hanti.  all: apply Hgamma_eq; *)
                (*                                                                                                                   reflexivity.  Qed. *)

  (** γ[LUB] is downward-closed: if c1 is below the bound, so is any c2 ≤ c1. *)
  Lemma gamma_downward (b : A) (c1 c2 : A) :
    c1 ∈ γ[ad] b -> c2 ≤ c1 -> c2 ∈ γ[ad] b.
  Proof using Hpre. simpl; unfold_set. move=> Hb Hc. by transitivity c1. Qed.

End LUB. End LUB.
Global Hint Unfold LUB.γ_lub : unfold_gamma.


(** * GLB (or unbounded). *)

Module GLBUnbounded. Section GLBUnbounded.

  Context {A : Type} (le : relation A) {Hpre : PreOrder le}.
  Local Notation "(≤)" := le (only parsing).
  Local Infix "≤" := le (at level 70).

  (** Extension of [≤] to [with_top A], where [Top] represents [−∞]
      (absence of lower bound).  [Top] is the smallest element. *)
  Definition leinf (a b : WithTop.with_top A) : Prop :=
    match a, b with
    | WithTop.Top, _ => True
    | WithTop.NotTop _, WithTop.Top => False
    | WithTop.NotTop x, WithTop.NotTop y => x ≤ y
    end.

  Infix "≤∞" := leinf (at level 70).

  Global Instance leinf_PreOrder : PreOrder leinf.
  Proof using A Hpre le.
    split.
    - move=> [|x] //=. reflexivity.
    - move=> [|x] [|y] [|z] //=. apply transitivity.
  Qed.

  (** Characterization of [γ] for GLBUnbounded using [≤∞]:
      [c ∈ γ(b)] iff [b ≤∞ NotTop c]. *)
  Lemma gammaE_leinf (b : WithTop.with_top A) (c : A) :
    c ∈ γ[WithTop.ad (GLB.ad le)] b <-> b ≤∞ WithTop.NotTop c.
  Proof using A le.
    destruct b as [|x]; simpl; unfold_set; reflexivity.
  Qed.

  (** This abstraction is interesting on unbounded sets, i.e. for
  which we can always find a lower elements. Otherwise, we can use
  Finite(⊥) as the smallest element of the set. *)

  (* TODO: state this as [a' ≤ a /\ ~ (a ≤ a')] instead, so as to avoid Leibniz
     equality here; antisymmetry would then no longer be required. *)
  Hypothesis unbounded : forall a : A, exists a' : A, a' ≤ a /\ ~ (a' = a).

  (** We assume antisymmetry wrt. leibniz equality. We could do it for
      other equivalence relations, but there are no uses for this for
      now. *)
  Hypothesis antisym: Antisymmetric A (=) le.

  Definition glb: abstract_domain A := GLB.ad le.
  Definition ad := WithTop.ad glb.

  (* No lower bound means that given any element, I can find a smaller
     one in S. This makes it easy to prove that S is unbounded. *)
  Definition no_lower_bound (S:℘ A) := forall z, exists z', z' ∈ S /\ z' ≤ z.

  (** Note that we cannot prove the converse unless we assume some
      classical logic. This is the direction that we are interested
      in: we want a way to prove that Top is the best abstraction, and
      the way is to prove that there is no lower bound.

      It means that we can only provide a weak is_α relation here: a
      relation that can prove, for some cases, that we have an
      IsAlpha, but may not prove this for every set and abstract
      element.  *)
  Theorem no_lower_bound_implies_top_is_best (S: ℘ A):
    no_lower_bound S -> IsAlpha (A:=ad) WithTop.Top S.
  Proof using A Hpre antisym le unbounded.
    rewrite is_alpha_iff_best_abstraction.
    move=> HSunbounded.
    split => //=.                (* Soundness is trivial. *)
    (* Need to prove that Top is the best abstraction. *)
    move=> a.
    case: a => //= => a.
    (* Only remains the case NotTop, which we must prove to be impossible. *)
    to_set. unfold_set. move => //=. unfold GLB.γ_glb. unfold_set.
    (* Remains: (forall c : A, c ∈ S -> a ≤ c) -> False *)
    move=> Ha_lb_S.              (* Hypothesis: a is lower bound of S. *)
    rewrite /no_lower_bound in HSunbounded.
    (* First: pick a' smaller than a, possible because the set is undounded. *)
    move: (unbounded a) => [a' [Ha'_le_a Ha'_ne_a]]. clear unbounded.
    (* Now: pick a'' smaller than a in S, possible because S is unbounded. *)
    move: (HSunbounded a') => [a'' [Ha''_in_S Ha''_le_a']].
    have Ha''_le_a: a'' ≤ a by transitivity a'.
    move: (Ha_lb_S a'' Ha''_in_S) => Ha_le_a''.
    (* we have a <= a'' <= a' <=a, so by anisymettry a = a' = a'', which contradicts a <> a'. *)
    by firstorder.
  Qed.


  (** The converse is false, unless <= is a total order and we assume classical axioms. *)
  (* Theorem top_is_best_implies_no_lower_bound (S: ℘ A): *)
  (*   IsAlpha (A:=glbtop) WithTop.Top S -> no_lower_bound S. *)
  (* Proof. *)
  (*   rewrite is_alpha_iff_best_abstraction.     *)
  (*   move=> [HOver HOptimal] a. clear HOver. (* No information in top overapproximates S. *) *)
  (*   (* Goal is to find an element in S smaller than a. *) *)
  (*   move: (HOptimal (WithTop.NotTop a)) => Hopt. *)
  (*   to_set in Hopt. cbv in Hopt. unfold_set in Hopt. simpl in Hopt. *)
     (* We have simplified Hopt to : (forall c : A, c ∈ S -> a ≤ c) -> False: it is false that a is a lower bound. *)
    (* Constructively, we could find an element c such that !(a <= c),
       and if <= is total, we would have c < a. But cannot be done
       non-constructively. *)

  Definition galois_glb : StrongAlphaRelation glb := (GLB.galois le).
  
  Definition is_α (αS:ad) (S:propset A) :=
    match αS with
    | WithTop.NotTop a => (@strong_α_relation A glb galois_glb) a S
    | WithTop.Top => no_lower_bound S
    end.

  Program Instance galoisW : WeakAlphaRelation ad :=
    { weak_α_relation := is_α }.
  Next Obligation.              (* It is a weak alpha relation. *)
    move: a H => [|a] H; rewrite /is_α in H.
    - by apply: no_lower_bound_implies_top_is_best.
    - rewrite is_alpha_iff_best_abstraction. to_set. firstorder.
      move: a0 H => [|a0 H] => //.
      hnf. firstorder.
  Qed.

  Next Obligation.              (* It allows rewriting with equivalent sets. *)
    move=> S1 S2. rewrite /is_α. case: a.
    - firstorder.
    - move=> a. apply: strong_α_proper.
  Qed.

  (** γ[GLBUnbounded] is upward-closed, inheriting from GLB via WithTop. *)
  Lemma gamma_upward (b : WithTop.with_top A) (c1 c2 : A) :
    c1 ∈ γ[ad] b -> c1 ≤ c2 -> c2 ∈ γ[ad] b.
  Proof. destruct b; simpl; [done | exact: GLB.gamma_upward]. Qed.

  (** GLBUnbounded is also an exact order. This depends on unbounded:
      if Top was equivalent to "greater than the lower bound", then we
      Top and <= glb would be equivalent in the concrete,
      and not in the abstract. *)
  Instance glbunbounded_is_included_exact : ExactOrder ad.
  Proof using A Hpre antisym le unbounded.
    move=> [|a2] [|a1]; simpl.
    - split; reflexivity.
    - (* Prove that False <-> WithTop.Top ⊑γ WithTop.NotTop a1.
         This comes from unbounded. *)
      split.
      + done.
      + rewrite /( _ ⊑γ _). unfold_set; unfold γ; simpl.
        have Hu := unbounded a1.
        move: Hu => [a2 [H2le1 Hneq]].
        move /(_ a2 I) => H1le2.
        move: (antisym a2 a1 H2le1 H1le2) => Heq.
        contradiction.
    - firstorder.
    - have Hg := (@GLB.glb_is_included_exact A le Hpre).
      unfold ExactOrder in Hg. unfold GLB.ad in Hg; simpl in Hg.
      rewrite Hg. rewrite /( _ ⊑γ _)/( _ ⊑γ _)/γ; simpl. done.
Qed.
  
End GLBUnbounded. End GLBUnbounded.

(** * LUB (or unbounded). *)

Module LUBUnbounded. Section LUBUnbounded.

  Context {A : Type} (le : relation A) {Hpre : PreOrder le}.
  Local Notation "(≤)" := le (only parsing).
  Local Infix "≤" := le (at level 70).

  Local Notation "(≥)" := (flip le) (only parsing).
  Local Infix "≥" := (flip le) (at level 70).

  (** Extension of [≤] to [with_top A], where [Top] represents [+∞]
      (absence of upper bound).  [Top] is the greatest element. *)
  Definition leinf (a b : WithTop.with_top A) : Prop :=
    match a, b with
    | _, WithTop.Top => True
    | WithTop.Top, WithTop.NotTop _ => False
    | WithTop.NotTop x, WithTop.NotTop y => x ≤ y
    end.

  Infix "≤∞" := leinf (at level 70).

  Global Instance leinf_PreOrder : PreOrder leinf.
  Proof using A Hpre le.
    split.
    - move=> [|x] //=. reflexivity.
    - move=> [|x] [|y] [|z] //=. apply transitivity.
  Qed.

  (** Characterization of [γ] for LUBUnbounded using [≤∞]:
      [c ∈ γ(b)] iff [NotTop c ≤∞ b]. *)
  Lemma gammaE_leinf (b : WithTop.with_top A) (c : A) :
    c ∈ γ[WithTop.ad (LUB.ad le)] b <-> WithTop.NotTop c ≤∞ b.
  Proof using A le.
    destruct b as [|x]; simpl; unfold_set; reflexivity.
  Qed.

  Hypothesis unbounded : forall a : A, exists a' : A, a' ≥ a /\ ~ (a' = a).

  (** We assume antisymmetry wrt. leibniz equality. We could do it for
      other equivalence relations, but there are no uses for this for
      now. *)
  Hypothesis antisym: Antisymmetric A (=) le.

  Definition antisym_flip: Antisymmetric A (=) (≥).
  Proof using A antisym le.  
    unfold Antisymmetric in *. move=> x y Hxy Hyx; apply antisym; assumption.
  Qed.
  
  Local Instance FlipPreOrder : PreOrder (≥).
  Proof using Hpre. by apply: flip_PreOrder. Qed.
  Local Definition glb_flip : abstract_domain A := GLBUnbounded.ad (≥). 

  Definition lub: abstract_domain A := LUB.ad le.
  Definition ad := WithTop.ad lub.

  
  Definition no_upper_bound (S:℘ A) := forall z, exists z', z' ∈ S /\ z' ≥ z.

  Theorem no_upper_bound_implies_top_is_best (S: ℘ A):
    no_upper_bound S -> IsAlpha (A:=ad) WithTop.Top S.
  Proof using A Hpre antisym le unbounded.
    have H: no_upper_bound S <-> GLBUnbounded.no_lower_bound (≥) S. by firstorder.
    rewrite H.
    apply: (GLBUnbounded.no_lower_bound_implies_top_is_best (≥)).
    - exact: unbounded.
    - exact: antisym_flip.
  Qed.

  Definition galois_lub : StrongAlphaRelation lub := (LUB.galois le).
  
  Definition is_α (αS:ad) (S:propset A) :=
    match αS with
    | WithTop.NotTop a => (@strong_α_relation A lub galois_lub) a S
    | WithTop.Top => no_upper_bound S
    end.

  Program Instance galoisW : WeakAlphaRelation ad :=
    { weak_α_relation := is_α }.
  Next Obligation.
    have H': GLBUnbounded.is_α (≥) a S.
    { destruct a; firstorder. }
    pose WA := GLBUnbounded.galoisW (≥) unbounded antisym_flip (Hpre:=FlipPreOrder).
    apply WA. done.
  Qed.

  Next Obligation.
    unfold is_α; case a.
    - firstorder.
    - move=> b. apply: strong_α_proper.
  Qed.

  (** γ[LUBUnbounded] is downward-closed, inheriting from LUB via WithTop. *)
  Lemma gamma_downward (b : WithTop.with_top A) (c1 c2 : A) :
    c1 ∈ γ[ad] b -> c2 ≤ c1 -> c2 ∈ γ[ad] b.
  Proof. destruct b; simpl; [done | exact: LUB.gamma_downward]. Qed.

  Instance lubunbounded_is_included_exact : ExactOrder ad.
  Proof using A Hpre antisym le unbounded.
    have H := GLBUnbounded.glbunbounded_is_included_exact (≥) unbounded antisym_flip (Hpre:=FlipPreOrder).
    exact H.
  Qed.

End LUBUnbounded. End LUBUnbounded.
  

(** * Bounded Interval. *)

Module Interval. Section Interval.

  Context {A : Type} (le : relation A) {Hpre : PreOrder le}.
  Local Notation "(≤)" := le (only parsing).
  Local Infix "≤" := le (at level 70).

  Definition glb : abstract_domain A := GLB.ad (≤).  
  Definition lub : abstract_domain A := LUB.ad (≤).

  Definition ad := Conjunction.ad glb lub.

End Interval. End Interval.  

(** * Unbounded Interval. *)

(** An unbounded interval is a conjunction of a GLBUnbounded and a
    LUBUnbounded bound.  This module contains only the parts that
    depend on a preorder; the abstract-lattice structure (join/meet)
    and the ExactOrder proof (which requires min/max) live in
    BoundLattice. *)
Module IntervalUnbounded. Section IntervalUnbounded.

  Context {A : Type} (le : relation A) {Hpre : PreOrder le}.
  Local Notation "(≤)" := le (only parsing).
  Local Infix "≤" := le (at level 70).

  Definition glbtop := GLBUnbounded.ad le.
  Definition lubtop := LUBUnbounded.ad le.

  (** The abstract domain (order + γ). *)
  Definition ad : abstract_domain A := Conjunction.ad glbtop lubtop.

  Definition interval := prod (WithTop.with_top A) (WithTop.with_top A).

  Definition non_bottom (i : interval) : Prop :=
    let (l, h) := i in
    match l with
    | WithTop.Top => True
    | WithTop.NotTop l =>
        match h with
        | WithTop.Top => True
        | WithTop.NotTop h => le l h
        end
    end.

  Definition nb_interval := { i : interval | non_bottom i }.

  Section Inhabited.
    (** We need a witness element for the (Top, Top) case. *)
    Context (inhabited_witness : A).

    Lemma non_bottom_non_empty :
      forall i : interval, non_bottom i <-> exists c, c ∈ γ[ad] i.
    Proof using inhabited_witness.
      move=> i; split.
      - move: i => [[|lowi] [|highi]] H.
        + exists inhabited_witness; unfold_set; done.
        + exists highi; unfold_set; split; [done | reflexivity].
        + exists lowi; unfold_set; split; [reflexivity | done].
        + exists lowi; unfold_set; split; [reflexivity | exact H].
      - move: i => [[|lowi] [|highi]] [c Hc] //=.
        unfold_set in Hc. move: Hc => [Hcl Hcr].
        by transitivity c.
    Qed.
  End Inhabited.

  (** Characterization of interval γ using the extended order ≤∞:
      c ∈ γ(lo, hi) iff lo ≤∞ NotTop c (GLB) and NotTop c ≤∞ hi (LUB). *)
  Lemma gammaE_leinf (lo hi : WithTop.with_top A) (c : A) :
    c ∈ γ[ad] (lo, hi) <->
    GLBUnbounded.leinf le lo (WithTop.NotTop c) /\
    LUBUnbounded.leinf le (WithTop.NotTop c) hi.
  Proof.
    rewrite Conjunction.gammaE.
    have Hl := GLBUnbounded.gammaE_leinf le lo c (Hpre:=Hpre).
    have Hh := LUBUnbounded.gammaE_leinf le hi c (Hpre:=Hpre).
    tauto.
  Qed.

  (** An interval is convex: if it contains [a] and [b], it contains every
      [x] with [a ≤ x ≤ b]. Both endpoint constraints relax through the
      transitivity of the extended order ≤∞. *)
  Lemma convex (i : interval) (a b x : A) :
    a ∈ γ[ad] i -> b ∈ γ[ad] i -> a ≤ x -> x ≤ b -> x ∈ γ[ad] i.
  Proof.
    case: i => lo hi.
    move=> /gammaE_leinf [Hlo _] /gammaE_leinf [_ Hhi] Hax Hxb.
    apply/gammaE_leinf. split.
    - transitivity (WithTop.NotTop a); [exact Hlo | exact Hax].
    - transitivity (WithTop.NotTop b); [exact Hxb | exact Hhi].
  Qed.

End IntervalUnbounded. End IntervalUnbounded.

(* Definition antitone {A: Type} (le : relation A) (f: A -> A) := *)
(*   ∀ (a:A) (a':A), le a a' -> le (f a') (f a). *)

(* (** We can compute the best abstraction of antitonic functions, *)
(*     e.g. unary minus, by taking the lub, when: - the glb b is also a *)
(*     minimum (b ∈ S) - the function is bijective. *)

(*     Otherwise, it may fail: e.g. if f(0) = 10, x ∈ (0-1] = 1, then the *)
(*     lub of f( (0-1]) is 1, even if f(0) = 10.*) *)
(* Lemma antitonic_lub {A: Type} {le : relation A} `{!PreOrder le} (f:A -> A) *)
(*   (Hantitone:antitone le f) b S : b ∈ S -> @is_glb A le b S -> @is_lub A le (f b) (fmap f S). *)
(* Proof. *)
(*   intros.  split. *)
(*   - intros. set_unfold. firstorder. subst. apply Hantitone. apply glb_is_lowerboud0. assumption. *)
(*   (* Prove minimality. *) *)
(*   - intro z'. intro Hin_fS_smaller_z'. set_unfold. *)
(*     apply Hin_fS_smaller_z'. exists b; split; [reflexivity|assumption]. *)
(* Qed. *)

(* TODO: pair this with a strictness flag, recording whether the glb is strict
   (open) or non-strict (closed). Useful for rationals, and possibly also when
   including -infinity. *)

(* An interval is a product of two opposite order relations, and that is exactly
   how it is built above: [Interval.ad] is [Conjunction.ad glb lub], and
   [IntervalUnbounded.ad] is [Conjunction.ad glbtop lubtop], where [glbtop] and
   [lubtop] adjoin a ⊤ (via [WithTop]) for sets with no lower / upper bound. *)


(** * Generic monotone-binop best-abstraction lemmas.

    Given a binary operator [f : A → B → C] monotone in both
    arguments, the minimum of the image set
    [{f a b | a ∈ S_A, b ∈ S_B}] equals [f a_A a_B] when [a_A], [a_B]
    are minima of [S_A], [S_B] — i.e. glbs that lie in their respective
    sets ([a_A ∈ S_A], [a_B ∈ S_B]). The symmetric statement holds for
    maxima (lubs in the set). These are the bare-preorder ingredients —
    no [Top], no [Conjunction] — used (after lifting through ∞ and
    combining into intervals) to derive best abstraction of
    [interval_add], the positive multiplication case, etc., from a
    single generic theorem. *)

Section MonotoneBinop.

  Context {A B C : Type}.
  Context (leA : relation A) (leB : relation B) (leC : relation C).
  Context {HpreA : PreOrder leA} {HpreB : PreOrder leB} {HpreC : PreOrder leC}.

  Definition monotone_binop (f : A -> B -> C) : Prop :=
    forall a1 a1' a2 a2',
      leA a1 a1' -> leB a2 a2' -> leC (f a1 a2) (f a1' a2').

  Lemma glb_monotone_binop
        (f : A -> B -> C) (Hmono : monotone_binop f)
        (SA : propset A) (SB : propset B) (aA : A) (aB : B) :
    GLB.is_glb leA aA SA ->
    GLB.is_glb leB aB SB ->
    aA ∈ SA -> aB ∈ SB ->
    GLB.is_glb leC (f aA aB) (collecting_binary_forward f SA SB).
  Proof using.
    move=> [HlbA HgrA] [HlbB HgrB] HAin HBin.
    split.
    - move=> z; unfold_set; move=> [c2 [c1 [Hc2 [Hc1 Heq]]]].
      rewrite -Heq. apply: Hmono.
      + exact: (HlbA _ Hc2).
      + exact: (HlbB _ Hc1).
    - move=> z Hz. apply: Hz. unfold_set. by exists aA, aB.
  Qed.

  Lemma lub_monotone_binop
        (f : A -> B -> C) (Hmono : monotone_binop f)
        (SA : propset A) (SB : propset B) (aA : A) (aB : B) :
    LUB.is_lub leA aA SA ->
    LUB.is_lub leB aB SB ->
    aA ∈ SA -> aB ∈ SB ->
    LUB.is_lub leC (f aA aB) (collecting_binary_forward f SA SB).
  Proof using.
    move=> [HubA HgrA] [HubB HgrB] HAin HBin.
    split.
    - move=> z; unfold_set; move=> [c2 [c1 [Hc2 [Hc1 Heq]]]].
      rewrite -Heq. apply: Hmono.
      + exact: (HubA _ Hc2).
      + exact: (HubB _ Hc1).
    - move=> z Hz. apply: Hz. unfold_set. by exists aA, aB.
  Qed.

End MonotoneBinop.

(** Extract [is_glb] / [is_lub] from the corresponding [WithTop]
    [IsAlpha] at a finite ([NotTop]) bound. *)
Lemma IsAlpha_glbtop_NotTop_is_glb {T : Type} (le : relation T) `{!PreOrder le}
      (l : T) (S : ℘ T) :
  IsAlpha (A:=GLBUnbounded.ad le) (WithTop.NotTop l) S -> GLB.is_glb le l S.
Proof.
  move=> H.
  apply (strong_α_relation_spec (StrongAlphaRelation:=GLB.galois le)).
  move=> a. exact: (H (WithTop.NotTop a)).
Qed.

Lemma IsAlpha_lubtop_NotTop_is_lub {T : Type} (le : relation T) `{!PreOrder le}
      (h : T) (S : ℘ T) :
  IsAlpha (A:=LUBUnbounded.ad le) (WithTop.NotTop h) S -> LUB.is_lub le h S.
Proof.
  move=> H.
  apply (strong_α_relation_spec (StrongAlphaRelation:=LUB.galois le)).
  move=> a. exact: (H (WithTop.NotTop a)).
Qed.


(** * "Glbs are mins" / "Lubs are maxs": universal attainment.

    [GlbsAreMins le] packages the fact that *every* set whose glb
    exists has that glb as a minimum — i.e. the glb lies in the set.
    Delivered in CPS to a [Stable] continuation so a domain without
    decidable membership can still route the witness through the
    [¬¬]-monad.

    Two concrete realisations:

    - **Discrete orders** ([Z], [N], machine integers): a [NotTop] glb
      [l] of [S] must be in [S] because otherwise [l+1] would still be
      a lower bound, contradicting maximality. The "+1" relies on a
      successor; this is the [Z_glbs_are_mins] route.

    - **Finite posets with decidable [le] and decidable membership**:
      enumerate the (finitely many) candidates and check membership
      directly. The continuation [Stable] hypothesis is then trivially
      discharged because membership is decidable. No successor is
      needed; finiteness substitutes for discreteness.

    [LubsAreMaxs] is dual (mirror argument on the maximum). *)
Class GlbsAreMins {A} (le : relation A) : Prop :=
  glbs_are_mins : forall (G : Prop) `{Stable G} (l : A) (S : ℘ A),
    GLB.is_glb le l S -> ((l ∈ S) -> G) -> G.

Class LubsAreMaxs {A} (le : relation A) : Prop :=
  lubs_are_maxs : forall (G : Prop) `{Stable G} (h : A) (S : ℘ A),
    LUB.is_lub le h S -> ((h ∈ S) -> G) -> G.


(** * Generic monotone-binop, ∞-aware ([WithTop] lifting).

    Extends [MonotoneBinop] to handle [WithTop] bounds ([GLBUnbounded]
    / [LUBUnbounded]).  Given a binary operator [f : A2 → A1 → A0]
    monotone and order-reflecting in both arguments, the best
    abstraction of the image set under [f] is computed pointwise by
    [WithTop.lift2 f].  The reach hypotheses characterize [f] at
    infinity: [reach_below_left f] means [f(−∞, b) = −∞], etc.

    Subscripts follow the [binary_alpha_complete] / [binary_best]
    convention: [2] is the first operand, [1] the second, [0] the
    result. *)

Section MonotoneBinopWithTop.

  Context {A2 A1 A0 : Type}.
  Context (le2 : relation A2) (le1 : relation A1) (le0 : relation A0).
  Context {Hpre2 : PreOrder le2} {Hpre1 : PreOrder le1} {Hpre0 : PreOrder le0}.

  (* Discreteness/antisymmetry are only needed on the CODOMAIN (A0):
     the attainment argument and Galois-connection appeal both fire
     there. The A2/A1 operands only need the preorder above. *)
  Context (unbounded_below0 : forall a : A0, exists a' : A0, le0 a' a /\ ~ (a' = a)).
  Context (unbounded_above0 : forall a : A0, exists a' : A0, le0 a a' /\ ~ (a' = a)).
  Context (antisym0 : Antisymmetric A0 (=) le0).

  (* Syntactic abbreviations: not generalized as Section parameters
     (unlike [Let]), so they don't leak into lemma signatures. *)
  Notation glbtop2 := (GLBUnbounded.ad le2).
  Notation glbtop1 := (GLBUnbounded.ad le1).
  Notation glbtop0 := (GLBUnbounded.ad le0).
  Notation lubtop2 := (LUBUnbounded.ad le2).
  Notation lubtop1 := (LUBUnbounded.ad le1).
  Notation lubtop0 := (LUBUnbounded.ad le0).

  (** [reach_below_left f] characterizes [f(−∞, b) = −∞]:
      for any [b] and target [z], we can find [a] with [f a b ≤ z]. *)
  Definition reach_below_left (f : A2 -> A1 -> A0) : Prop :=
    forall b z, exists a, le0 (f a b) z.

  (** [reach_below_right f] characterizes [f(a, −∞) = −∞]. *)
  Definition reach_below_right (f : A2 -> A1 -> A0) : Prop :=
    forall a z, exists b, le0 (f a b) z.

  (** [reach_above_left f] characterizes [f(+∞, b) = +∞]. *)
  Definition reach_above_left (f : A2 -> A1 -> A0) : Prop :=
    forall b z, exists a, le0 z (f a b).

  (** [reach_above_right f] characterizes [f(a, +∞) = +∞]. *)
  Definition reach_above_right (f : A2 -> A1 -> A0) : Prop :=
    forall a z, exists b, le0 z (f a b).

  (** [order_reflecting_left f] means [f a b ≤ f a' b → a ≤ a']. *)
  Definition order_reflecting_left (f : A2 -> A1 -> A0) : Prop :=
    forall a a' b, le0 (f a b) (f a' b) -> le2 a a'.

  (** [order_reflecting_right f] means [f a b ≤ f a b' → b ≤ b']. *)
  Definition order_reflecting_right (f : A2 -> A1 -> A0) : Prop :=
    forall a b b', le0 (f a b) (f a b') -> le1 b b'.

  (** [attained S l] says the bound [l] is realised inside [S]: an
      element-of-S for finite bounds, just non-emptiness for [Top].

      The predicate is directionally neutral: paired with [is_glb] it
      states that [l] is the *minimum* of [S]; paired with [is_lub] it
      states that [l] is the *maximum*. Same predicate, both roles. *)
  Definition attained {T} (S : ℘ T) (l : WithTop.with_top T) : Prop :=
    match l with
    | WithTop.NotTop a => a ∈ S
    | WithTop.Top => exists c, c ∈ S
    end.

  Lemma attained_witness {T} (S : ℘ T) l : attained S l -> exists c, c ∈ S.
  Proof. case: l => [|a] H; [exact: H | by exists a]. Qed.

  (** [interval_lift2 f] lifts [f] to interval bounds, componentwise via
      [WithTop.lift2]: the low bound of the result is [f] of the low
      bounds, the high bound [f] of the high bounds.  Used as the
      abstract transfer function [fA] in the interval lemmas below. *)
  Definition interval_lift2 (f : A2 -> A1 -> A0)
      (i2 : WithTop.with_top A2 * WithTop.with_top A2)
      (i1 : WithTop.with_top A1 * WithTop.with_top A1)
      : WithTop.with_top A0 * WithTop.with_top A0 :=
    (WithTop.lift2 f (fst i2) (fst i1), WithTop.lift2 f (snd i2) (snd i1)).

  (** Design note — the [attained] hypotheses and where they fail.

      The lemmas below take four [attained] facts as plain hypotheses.
      Discharging them is the whole content of [GlbsAreMins] /
      [LubsAreMaxs]: an [attained] glb is a minimum, an [attained] lub
      a maximum. The [itv_attained_low/high_witness] helpers
      after this section discharge them generically from those
      classes (plus [Stable] on the conclusion).

      The classes — and so the proofs that use [attained] — only fire
      on DISCRETE orders. The two concrete recipes:

      - **Discrete orders** ([Z], [N], machine ints): from [is_glb l S],
        [l ∈ S] follows because otherwise [l+1] would still be a lower
        bound, contradicting maximality. The "+1" requires a successor.

      - **Finite posets** with decidable [le] and decidable membership:
        enumerate to decide [l ∈ S] directly; finiteness substitutes
        for discreteness.

      The argument breaks on DENSE orders. For OPEN intervals over a
      dense order (e.g. open Q intervals) [attained] is genuinely
      *false*: [l ∉ γ((l,h))]. The proof would have to be redone:

      - the "[f a b] is the glb" step currently exhibits [f aA aB] as
        an *element* of the image, needing [aA ∈ SA], [aB ∈ SB]. On
        open intervals that element doesn't exist;
      - it must instead be an ε-approximation argument: from
        [l = glb S], [l + ε] is not a lower bound, so some element of
        [S] lies within ε of [l]; combining two such elements
        contradicts any lower bound strictly above [l1 + l2].

      That argument needs strictly more than the current signature:

      - [attained] would weaken to *approachability*
        [∀ ε > 0, ∃ a ∈ S, leC a (l + ε)] (satisfied by closed Z and
        open Q intervals alike);
      - the codomain can no longer be an arbitrary preorder — the
        [+ ε] machinery requires a dense ordered-group structure;
      - [f] must be assumed CONTINUOUS, not merely monotone and
        order-reflecting: a discontinuous order-reflecting [f] makes
        α-completeness fail on open intervals outright.

      So dense / open-interval domains are a separate development
      with extra assumptions on [f] and on the carrier; they are not
      a free generalisation of [GlbsAreMins] / [LubsAreMaxs]. *)

  (** ** [IsAlpha] for [WithTop.lift2] on [GLBUnbounded] (∞-aware single bound).

      Stated as [binary_alpha_complete] (arguments in [2 → 1 → 0]
      order): given the [attained]/[reach] structural facts, mapping
      the best abstractions of [S2], [S1] through [WithTop.lift2 f]
      yields the best abstraction of the image. *)
  Lemma glbtop_lift2_monotone_alpha_complete
        (f : A2 -> A1 -> A0) (Hmono : monotone_binop le2 le1 le0 f)
        (Hrefl : order_reflecting_left f) (Hrefr : order_reflecting_right f)
        (l2 : WithTop.with_top A2) (l1 : WithTop.with_top A1)
        (S2 : ℘ A2) (S1 : ℘ A1) :
    attained S2 l2 -> attained S1 l1 ->
    reach_below_left f -> reach_below_right f ->
    binary_alpha_complete glbtop2 glbtop1 glbtop0
      (WithTop.lift2 f) (collecting_binary_forward f) l2 l1 S2 S1.
  Proof using A2 A1 A0 Hpre2 Hpre1 Hpre0 le2 le1 le0 unbounded_below0 antisym0.
    rewrite /binary_alpha_complete.
    move=> Hatt2 Hatt1 HreachL HreachR H2 H1.
    have [w2 Hw2] := attained_witness _ _ Hatt2.
    have [w1 Hw1] := attained_witness _ _ Hatt1.
    case: l2 l1 H2 H1 Hatt2 Hatt1 => [|aA] [|aB] H2 H1 Hatt2 Hatt1.
    1-3: rewrite is_alpha_iff_best_abstraction; split; first done;
         move=> [|c] //= Himg.
    - (* (Top, Top) *)
      have [a0 Ha0] := HreachL w1 c.
      apply: (proj1 (H2 (WithTop.NotTop a0))) => a Ha.
      apply: (Hrefl a0 a w1); transitivity c => //.
      apply: Himg; unfold_set; by exists a, w1.
    - (* (Top, NotTop aB) *)
      have [a0 Ha0] := HreachL aB c.
      apply: (proj1 (H2 (WithTop.NotTop a0))) => a Ha.
      apply: (Hrefl a0 a aB); transitivity c => //.
      apply: Himg; unfold_set; by exists a, aB.
    - (* (NotTop aA, Top) *)
      have [b0 Hb0] := HreachR aA c.
      apply: (proj1 (H1 (WithTop.NotTop b0))) => b Hb.
      apply: (Hrefr aA b0 b); transitivity c => //.
      apply: Himg; unfold_set; by exists aA, b.
    - (* (NotTop aA, NotTop aB) *)
      have HglbA := IsAlpha_glbtop_NotTop_is_glb le2 aA S2 H2.
      have HglbB := IsAlpha_glbtop_NotTop_is_glb le1 aB S1 H1.
      apply: (weak_α_relation_spec
                (WeakAlphaRelation:=GLBUnbounded.galoisW le0 unbounded_below0 antisym0)
                (WithTop.NotTop (f aA aB))).
      exact: glb_monotone_binop le2 le1 le0 f Hmono S2 S1 aA aB
               HglbA HglbB Hatt2 Hatt1.
  Qed.

  (** ** [IsAlpha] for [WithTop.lift2] on [LUBUnbounded] (∞-aware single bound).
      Symmetric to [glbtop_lift2_monotone_alpha_complete] (directions of [Hrefl]/
      [Hrefr] and transitivity flipped). *)
  Lemma lubtop_lift2_monotone_alpha_complete
        (f : A2 -> A1 -> A0) (Hmono : monotone_binop le2 le1 le0 f)
        (Hrefl : order_reflecting_left f) (Hrefr : order_reflecting_right f)
        (l2 : WithTop.with_top A2) (l1 : WithTop.with_top A1)
        (S2 : ℘ A2) (S1 : ℘ A1) :
    attained S2 l2 -> attained S1 l1 ->
    reach_above_left f -> reach_above_right f ->
    binary_alpha_complete lubtop2 lubtop1 lubtop0
      (WithTop.lift2 f) (collecting_binary_forward f) l2 l1 S2 S1.
  Proof using A2 A1 A0 Hpre2 Hpre1 Hpre0 le2 le1 le0 unbounded_above0 antisym0.
    rewrite /binary_alpha_complete.
    move=> Hatt2 Hatt1 HreachL HreachR H2 H1.
    have [w2 Hw2] := attained_witness _ _ Hatt2.
    have [w1 Hw1] := attained_witness _ _ Hatt1.
    case: l2 l1 H2 H1 Hatt2 Hatt1 => [|aA] [|aB] H2 H1 Hatt2 Hatt1.
    1-3: rewrite is_alpha_iff_best_abstraction; split; first done;
         move=> [|c] //= Himg.
    - (* (Top, Top) *)
      have [a0 Ha0] := HreachL w1 c.
      apply: (proj1 (H2 (WithTop.NotTop a0))) => a Ha.
      apply: (Hrefl a a0 w1); transitivity c => //.
      apply: Himg; unfold_set; by exists a, w1.
    - (* (Top, NotTop aB) *)
      have [a0 Ha0] := HreachL aB c.
      apply: (proj1 (H2 (WithTop.NotTop a0))) => a Ha.
      apply: (Hrefl a a0 aB); transitivity c => //.
      apply: Himg; unfold_set; by exists a, aB.
    - (* (NotTop aA, Top) *)
      have [b0 Hb0] := HreachR aA c.
      apply: (proj1 (H1 (WithTop.NotTop b0))) => b Hb.
      apply: (Hrefr aA b b0); transitivity c => //.
      apply: Himg; unfold_set; by exists aA, b.
    - (* (NotTop aA, NotTop aB) *)
      have HlubA := IsAlpha_lubtop_NotTop_is_lub le2 aA S2 H2.
      have HlubB := IsAlpha_lubtop_NotTop_is_lub le1 aB S1 H1.
      apply: (weak_α_relation_spec
                (WeakAlphaRelation:=LUBUnbounded.galoisW le0 unbounded_above0 antisym0)
                (WithTop.NotTop (f aA aB))).
      exact: lub_monotone_binop le2 le1 le0 f Hmono S2 S1 aA aB
               HlubA HlubB Hatt2 Hatt1.
  Qed.

  (** ** [IsAlpha] for the interval (Conjunction of glbtop and lubtop).

      Stated as [binary_alpha_complete] with the abstract transfer
      function [interval_lift2 f] and arguments in [2 → 1 → 0] order. *)
  Lemma interval_lift2_monotone_alpha_complete
        (f : A2 -> A1 -> A0) (Hmono : monotone_binop le2 le1 le0 f)
        (Hrefl : order_reflecting_left f) (Hrefr : order_reflecting_right f)
        (l2 h2 : WithTop.with_top A2) (l1 h1 : WithTop.with_top A1)
        (S2 : ℘ A2) (S1 : ℘ A1) :
    attained S2 l2 -> attained S2 h2 -> attained S1 l1 -> attained S1 h1 ->
    reach_below_left f -> reach_below_right f ->
    reach_above_left f -> reach_above_right f ->
    binary_alpha_complete
      (Conjunction.ad glbtop2 lubtop2) (Conjunction.ad glbtop1 lubtop1)
      (Conjunction.ad glbtop0 lubtop0)
      (interval_lift2 f) (collecting_binary_forward f)
      (l2, h2) (l1, h1) S2 S1.
  Proof using A2 A1 A0 Hpre2 Hpre1 Hpre0 le2 le1 le0
            unbounded_below0 unbounded_above0 antisym0.
    rewrite /binary_alpha_complete /interval_lift2 /=.
    move=> Hattl2 Hatth2 Hattl1 Hatth1 Hrbl Hrbr Hral Hrar Ha2 Ha1.
    move/Conjunction.is_alpha_pair_iff: Ha2 => [Hl2 Hh2].
    move/Conjunction.is_alpha_pair_iff: Ha1 => [Hl1 Hh1].
    apply Conjunction.is_alpha_pair_iff; split.
    - by apply: glbtop_lift2_monotone_alpha_complete.
    - by apply: lubtop_lift2_monotone_alpha_complete.
  Qed.

  (** ** Generic [binary_best] packaging.

      On a canonical domain — every element is the best abstraction of
      its own [γ] — whose bounds are attained, a monotone,
      order-reflecting, ±∞-reaching [f] yields the best abstraction of
      the image set, i.e. [interval_lift2 f] satisfies [binary_best].
      Unlike the [exact ⇒ best] route this also covers operators that
      are sound but not exact (e.g. multiplication, whose image of two
      intervals need not be an interval). *)
  Lemma interval_lift2_monotone_binary_best
        (f : A2 -> A1 -> A0) (Hmono : monotone_binop le2 le1 le0 f)
        (Hrefl : order_reflecting_left f) (Hrefr : order_reflecting_right f)
        (Hrbl : reach_below_left f) (Hrbr : reach_below_right f)
        (Hral : reach_above_left f) (Hrar : reach_above_right f)
        (Hcanon2 : forall i, BestAbstraction (A:=Conjunction.ad glbtop2 lubtop2)
                               i (γ[Conjunction.ad glbtop2 lubtop2] i))
        (Hcanon1 : forall i, BestAbstraction (A:=Conjunction.ad glbtop1 lubtop1)
                               i (γ[Conjunction.ad glbtop1 lubtop1] i))
        (Hatt2 : forall i, attained (γ[Conjunction.ad glbtop2 lubtop2] i) (fst i)
                        /\ attained (γ[Conjunction.ad glbtop2 lubtop2] i) (snd i))
        (Hatt1 : forall i, attained (γ[Conjunction.ad glbtop1 lubtop1] i) (fst i)
                        /\ attained (γ[Conjunction.ad glbtop1 lubtop1] i) (snd i)) :
    binary_best (Conjunction.ad glbtop2 lubtop2) (Conjunction.ad glbtop1 lubtop1)
                (Conjunction.ad glbtop0 lubtop0)
                (interval_lift2 f) (collecting_binary_forward f).
  Proof using A2 A1 A0 Hpre2 Hpre1 Hpre0 le2 le1 le0
            unbounded_below0 unbounded_above0 antisym0.
    move=> a2 a1.
    case: a2 (Hcanon2 a2) (Hatt2 a2)
      => l2 h2 /best_abstraction_is_is_alpha Hc2 [Hattl2 Hatth2].
    case: a1 (Hcanon1 a1) (Hatt1 a1)
      => l1 h1 /best_abstraction_is_is_alpha Hc1 [Hattl1 Hatth1].
    apply: is_alpha_is_best_abstraction.
    by apply: (interval_lift2_monotone_alpha_complete f Hmono Hrefl Hrefr
              l2 h2 l1 h1).
  Qed.

End MonotoneBinopWithTop.

(** * Attainment witnesses for interval bounds.

    Generic over any preorder [le] equipped with [GlbAttaining le] and
    [LubAttaining le]. From an [IsAlpha] on an interval [(l, h)] and a
    non-emptiness witness, extract an [attained] fact for the chosen
    bound, in CPS form against a [Stable] continuation.

    For a [NotTop] bound the [Glb/LubAttaining] principle fires; for a
    [Top] bound the non-emptiness witness suffices. This is the
    recommended entry point for proving best abstraction of an interval
    transfer function: it discharges the four [attained] obligations of
    [interval_lift2_monotone_alpha_complete] without requiring decidable
    membership on the abstracted set. *)
Section ItvAttained.

  Context {A : Type} {le : relation A} `{!PreOrder le}.
  Context `{!GlbsAreMins le} `{!LubsAreMaxs le}.

  Lemma itv_attained_low_witness {G : Prop} `{Stable G}
    (l h : WithTop.with_top A) (S : ℘ A) :
    IsAlpha (A:=IntervalUnbounded.ad le) (l, h) S ->
    (exists c, c ∈ S) -> (attained S l -> G) -> G.
  Proof using A le PreOrder0 GlbsAreMins0.
    move=> Ha [w Hw] Hk.
    case: l Ha Hk => [|a] Ha Hk; first by apply: Hk; exists w.
    move/Conjunction.is_alpha_pair_iff: Ha => [Hglb _].
    apply: (glbs_are_mins _ a S); last exact: Hk.
    exact: IsAlpha_glbtop_NotTop_is_glb Hglb.
  Qed.

  Lemma itv_attained_high_witness {G : Prop} `{Stable G}
    (l h : WithTop.with_top A) (S : ℘ A) :
    IsAlpha (A:=IntervalUnbounded.ad le) (l, h) S ->
    (exists c, c ∈ S) -> (attained S h -> G) -> G.
  Proof using A le PreOrder0 LubsAreMaxs0.
    move=> Ha [w Hw] Hk.
    case: h Ha Hk => [|a] Ha Hk; first by apply: Hk; exists w.
    move/Conjunction.is_alpha_pair_iff: Ha => [_ Hlub].
    apply: (lubs_are_maxs _ a S); last exact: Hk.
    exact: IsAlpha_lubtop_NotTop_is_lub Hlub.
  Qed.

End ItvAttained.
