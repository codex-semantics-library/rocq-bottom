Require Import Abstraction.
Require Import AbstractLattice.
Require Import ssreflect ssrbool ssrfun.
Require Import base.
Require Import autoreflect.
Set Primitive Projections.

(** ** WithTop.

 Take an abstraction/abstract_domain/abstract_lattice, and add a top element. *)
Module WithTop.

  Inductive with_top (A:Type) :=
  | Top : with_top A
  | NotTop: A -> with_top A.

  Arguments Top {A}.
  Arguments NotTop {A} _.  

  Definition lift2 {A B C} (f: A -> B -> C) (a: with_top A) (b: with_top B) : with_top C :=
    match a,b with
    | Top, _ | _, Top => Top
    | NotTop a, NotTop b => NotTop (f a b)
    end.
      
  (** *** Abstraction. *)
  Section Abs.
    Context {C : Type} (A: abstraction C).
    Definition gamma (a:with_top A) :=
      match a with
      | Top => full_set
      | NotTop a => γ[A] a
      end.

    Definition abs : abstraction C :=
      BuildAbstraction gamma.

    Global Instance gammaP inA:
      (forall (x:C) a, AutoReflect(x ∈ γ[A] a)(inA a x)) ->
      (forall x a, AutoReflect(x ∈ γ[abs] a)
                (match a with
                 | Top => true
                 | NotTop a => inA a x
                 end)).
    Proof.
      move=> H x a.
      case: a.
      - apply: (iffP idP); firstorder.
      - apply/H.
    Qed.
    
  End Abs.

  (** *** Abstract domain. *)  
  Section AD.
    Context {C : Type} (A: abstract_domain C).

    Definition is_included (a1 a2: with_top A) : Prop :=
      match a2 with
      | Top => True
      | NotTop a2 => 
          match a1 with
          | Top => False
          | NotTop a1 => a1 ⊑[A] a2
          end
      end.
    
    Definition laws : abstract_domain_laws (γ[abs A] ) is_included.
    Proof.
      refine {| ad_sqsubseteq_preorder := _ |}.
      (* Order-preservation. *)
      { to_set. move=> [|a1] [|a2] //=. rewrite /is_included. by apply order_preserving. }
      Unshelve.
      (* sqsubseteq preorder. *)
        split.
        + move=> [|x] => //=. rewrite /is_included. reflexivity.
        + move=> [|x] [|y] [|z] //= ??. rewrite /is_included. by transitivity y.
    Qed.
    
    Definition ad : abstract_domain C :=
      BuildAbstractDomain (γ[abs A] ) is_included laws.

    Global Instance is_includedP is_includedb :
      (forall a1 a2, AutoReflect(a1 ⊑[A] a2)(is_includedb a1 a2)) ->
      (forall a1 a2, AutoReflect(a1 ⊑[ad] a2)(match a2 with
                    | Top => true
                    | NotTop a2 =>
                        match a1 with
                        | Top => false
                        | NotTop a1 => is_includedb a1 a2
                        end end)).
    Proof.
      move=> H a1 a2; rewrite /is_included.
      case: a2 => [|a2]; simpl.
      - (* a2 = Top *) by apply: (iffP idP).
      - (* a2 = NotTop a2 *)
        case: a1 => [|a1]; simpl.
        + (* a1 = Top *) by apply: (iffP idP).
        + (* a1 = NotTop a1 *) exact: H.
    Qed.

    (** If we can specify when [Top] is an adjunction (i.e., we can say
        when Top is the best approximation for a set, i.e. when no
        element of [A] can be used), then we can lift the galois
        connection on [A] to the galois connection on [A+⊤].

        Note: [Top] is obviously an overapproximation, so the
        difficulty is proving that it is the best abstraction,
        i.e. that it is an [UpperBoundInPrecision]. *)
    Instance galois `{E:!@StrongAlphaRelation C A} (P: ℘ C -> Prop)
      (HP: forall S, P S <-> IsAlpha (A:=ad) Top S) : StrongAlphaRelation (ad).
    Proof.
      move: E => [is_α His_α].
      refine {| strong_α_relation (a:ad) S :=
                 match a with
                 | Top => P S
                 | NotTop a => is_α a S
                 end|}.
      move=> a S.
      case: a.
        exact (HP S).
      - move=> αS. rewrite His_α; clear His_α. to_set.
        split.
        + move=> H a. case: a => [|a] => //=.
        + move=> H a. apply: (H (NotTop a)).
    Defined.
  End AD.

  (** *** Abstract join semilattice. *)
  Section AJSL.
    Context {C : Type} (AJSL: abstract_join_semilattice C).

    Let inner_abs : abstraction C := BuildAbstraction (γ[AJSL] ).
    Let inner_ad : abstract_domain C := abstract_join_semilattice_to_abstract_domain AJSL.

    (** Join absorbs Top (like union with the full set). *)
    Definition join := lift2 (ajsl_join AJSL).

    Definition equiv (a b: with_top AJSL) : Prop :=
      match a, b with
      | Top, Top => True
      | NotTop a, NotTop b => ajsl_equiv AJSL a b
      | _, _ => False
      end.

    Instance ajsl_laws :
      @abstract_join_semilattice_laws C (ad inner_ad) join equiv.
    Proof.
      refine {| ajsl_ad_laws := _ |}.
      - move=> [|a1] [|a2] //= H. exact (ajsl_equiv_compat _ _ H).
      - move=> [|a1] [|a2] //=. exact (ajsl_join_compat_l a1 a2).
      - move=> [|a1] [|a2] //=. exact (ajsl_join_compat_r a1 a2).
    Qed.

    Definition ajsl : abstract_join_semilattice C :=
      BuildAbstractJoinSemilattice (ad inner_ad) join equiv ajsl_laws.

    Instance WithTop_JoinIsLUB `{HLUB:!JoinIsLUB AJSL} : JoinIsLUB ajsl.
    Proof.
      move=> [|a1] [|a2] [|c] //= H1 H2. exact (join_lub a1 a2 c H1 H2).
    Qed.
  End AJSL.

  (** *** Abstract lattice. *)
  Section AL.
    Context {C : Type} (AL: abstract_lattice C).

    (** Meet treats Top as neutral (intersecting with the full set changes nothing). *)
    Definition meet (a b: with_top AL) : with_top AL :=
      match a, b with
      | Top, x | x, Top => x
      | NotTop a, NotTop b => NotTop (al_meet AL a b)
      end.

    Definition al : abstract_lattice C :=
      MkAbstractLattice (ajsl (al_ajsl AL)) meet.
  End AL.

End WithTop.
Global Hint Unfold WithTop.gamma : unfold_gamma.


(** ** WithBottom.

 Dual of [WithTop]: take an abstraction/abstract_domain and add a bottom
 element representing the empty concrete set. Useful for operations that
 can genuinely produce an empty result (e.g. partial semantics such as
 division when the divisor set is {0}). *)
Module WithBottom.

  Inductive with_bottom (A : Type) :=
  | Bot : with_bottom A
  | NotBot : A -> with_bottom A.

  Arguments Bot {A}.
  Arguments NotBot {A} _.

  Definition lift2 {A} (f : A -> A -> A) (a b : with_bottom A) :=
    match a, b with
    | Bot, _ | _, Bot => Bot
    | NotBot a, NotBot b => NotBot (f a b)
    end.

  (** *** Abstraction. *)
  Section Abs.
    Context {C : Type} (A : abstraction C).
    Definition gamma (a : with_bottom A) : propset C :=
      match a with
      | Bot => ∅
      | NotBot a => γ[A] a
      end.

    Definition abs : abstraction C :=
      BuildAbstraction gamma.
  End Abs.

  (** *** Abstract domain. *)
  Section AD.
    Context {C : Type} (A : abstract_domain C).

    (** [Bot] is below everything. *)
    Definition is_included (a1 a2 : with_bottom A) : Prop :=
      match a1 with
      | Bot => True
      | NotBot a1 =>
          match a2 with
          | Bot => False
          | NotBot a2 => a1 ⊑[A] a2
          end
      end.

    Definition laws : abstract_domain_laws (γ[abs A] ) is_included.
    Proof.
      refine {| ad_sqsubseteq_preorder := _ |}.
      (* Order-preservation. *)
      { move=> [|a1] [|a2] H //=. simpl in H. by apply order_preserving. }
      Unshelve.
      (* PreOrder. *)
      split.
      - move=> [|x] //=. reflexivity.
      - move=> [|x] [|y] [|z] //=. by transitivity y.
    Qed.

    Definition ad : abstract_domain C :=
      BuildAbstractDomain (γ[abs A] ) is_included laws.

    (** Lift a best abstraction from [A] through [NotBot]. *)
    Lemma BestAbstraction_NotBot (a : A) (S : propset C) :
      (exists c, c ∈ S) ->
      BestAbstraction (A:=A) a S ->
      BestAbstraction (A:=ad) (NotBot a) S.
    Proof.
      move=> [c0 Hc0] [Hover Hmin]. split.
      - move=> c Hc. exact: Hover.
      - move=> [|a'] Ha'; simpl in *.
        + exfalso. have := Ha' c0 Hc0. by rewrite propset_elem_of_iff.
        + exact: Hmin.
    Qed.

    (** [Bot] is the best abstraction of the empty set. *)
    Lemma BestAbstraction_Bot (S : propset C) :
      (forall c, c ∈ S -> False) ->
      BestAbstraction (A:=ad) Bot S.
    Proof.
      move=> Hempty. split.
      - move=> c Hc. by exfalso; apply: Hempty Hc.
      - by move=> [|a'].
    Qed.
  End AD.

End WithBottom.
Global Hint Unfold WithBottom.gamma : unfold_gamma.


(** ** CollapsedBottom.

    Many abstract domains have a representability problem at the
    bottom: the *true* most-precise abstraction of [∅] either does not
    exist as a single syntactic element of the carrier, or has several
    syntactic witnesses that are not [⊑]-comparable. For intervals,
    every [(NotTop l, NotTop h)] with [l > h] has [γ ≡ ∅], yet none is
    [⊑] all others (the [(1, 0)] interval is not below [(5, 5)] in
    the inherited order, and the best interval [+oo,-oo] is not
    representable). For reduced products, the empty case has even
    more syntactic representatives ([⊥] paired with any congruence is
    empty).

    There are two distinct fixes to this problem, which we provide as
    two separate combinators:

    - [CollapsedBottom] (this module) widens the abstract order so
      that every γ-empty element is below everything. The carrier is
      unchanged: every existing γ-empty element acts as a (semantic)
      bottom and they are all [⊑]-equivalent in the new order. This
      is what the order-theoretic structure usually wants. It does
      not require a subset type and emptiness checking remains fast,
      but there is no syntactically distinguished bottom and one
      cannot check for bottom by equality.

    - [CanonicalBottom] (defined further below, after [Subset])
      restricts the carrier via [Subset] to a single chosen γ-empty
      representative [bot] together with the non-empty elements. This
      gives a syntactic canonical bottom that can be tested by
      equality, at the price of a subset type and a smart constructor
      to project arbitrary elements back into the canonical form.

    The two are independent and compose: one can [Subset]-canonicalize
    first (to obtain a unique γ-empty representative) and then
    [CollapsedBottom]-widen the order (to make that representative a
    true [⊑]-minimum). Z_interval and ZIntervalCongruence do exactly
    this.

    Note: [WithBottom] is a third, unrelated approach that adds a
    fresh [Bot] constructor at the type level. *)
Module CollapsedBottom.

  Section AD.
    Context {C : Type} (A : abstract_domain C).

    Definition is_empty (a : A) : Prop := γ[A] a ⊆⊇ ∅.

    (** Modified order: γ-empty elements are below everything. *)
    Definition is_included (a1 a2 : A) : Prop :=
      is_empty a1 \/ a1 ⊑[A] a2.

    Definition laws : abstract_domain_laws (γ[A] ) is_included.
    Proof.
      refine {| ad_sqsubseteq_preorder := _ |}.
      (* Soundness: a1 ⊑ a2 → γ a1 ⊆ γ a2. *)
      { move=> a1 a2 [Hempty | H] c Hc.
        - exfalso. exact: (proj1 Hempty c Hc).
        - by apply: (ad_γ_order_preserving a1 a2 H). }
      Unshelve.
      (* PreOrder. *)
      split.
      - move=> a. right. reflexivity.
      - move=> a1 a2 a3 H12 H23.
        case: H12 => [H12 | H12].
        + by left.
        + case: H23 => [H23 | H23].
          * left. split=> c Hc; last by [].
            apply (proj1 H23 c).
            exact: (ad_γ_order_preserving a1 a2 H12 c Hc).
          * right. by transitivity a2.
    Qed.

    Definition ad : abstract_domain C :=
      BuildAbstractDomain (γ[A] ) is_included laws.

    (** Any γ-empty element is MaximallyReduced in the new order:
        every element with the same (empty) concretization is above. *)
    Lemma is_empty_maximally_reduced (a : A) :
      is_empty a -> @MaximallyReduced C ad a.
    Proof.
      move => Hemp. split.
      - done.
      - move => a' Ha'. by left.
    Qed.

    (** For a non-empty [S], being a best abstraction in the
        widened-order domain coincides with being one in the
        underlying domain: the γ-empty collapse only changes the order
        on γ-empty elements, and neither [α S] nor any
        overapproximation of a non-empty [S] is γ-empty. *)
    Lemma collapsedbottom_is_alpha (a : A) (S : propset C) :
      (exists c, c ∈ S) ->
      (IsAlpha (A:=ad) a S <-> IsAlpha (A:=A) a S).
    Proof.
      move=> [w Hw].
      have not_empty_of_sub : forall a', S ⊆ γ[A] a' -> ~ is_empty a'.
      { move=> a' Hsub [Hemp _]. exact: (Hemp w (Hsub w Hw)). }
      split.
      - move=> H a'. split.
        + move=> HS. case: (proj1 (H a') HS) => [Hemp | Hle]; last exact: Hle.
          exfalso.
          exact: (not_empty_of_sub a
                   (proj2 (H a) (or_intror (reflexivity a))) Hemp).
        + move=> Hle. apply: (proj2 (H a')). by right.
      - move=> H a'. split.
        + move=> HS. right. exact: proj1 (H a') HS.
        + case=> [Hemp | Hle].
          * exfalso.
            exact: (not_empty_of_sub a (proj2 (H a) (reflexivity a)) Hemp).
          * exact: proj2 (H a') Hle.
    Qed.

    (** ExactOrder for CollapsedBottom: holds whenever the underlying
        domain is ExactOrder on its non-empty side, and emptiness is
        decidable. The hypothesis [Hexact_pos] is the "ExactOrder
        restricted to non-empty witnesses" property — strictly weaker
        than [ExactOrder A], which would make [CollapsedBottom]
        redundant (a γ-empty element would already be ⊑[A] anything). *)
    Instance CollapsedBottom_ExactOrder
      (is_empty_dec : forall a : A, {is_empty a} + {~ is_empty a})
      (Hexact_pos : forall a1 a2 : A,
          ~ is_empty a1 -> γ[A] a1 ⊆ γ[A] a2 -> a1 ⊑[A] a2)
      : ExactOrder ad.
    Proof.
      move=> a1 a2. split.
      - exact: (sound_order (A:=ad)).
      - move=> H. 
        case: (is_empty_dec a1) => Hemp.
        + by left.
        + right. exact: Hexact_pos.
    Qed.
  End AD.

  (** Lift a join-semilattice: same join, same equiv, widened ⊑.
      Note: with this definition [JoinIsLUB] does NOT lift from the
      underlying [AJSL] in general — see counter-example below.
      For a [JoinIsLUB]-preserving variant, use [ajsl_lub] below,
      which redefines join so γ-empty elements act as identities. *)
  Section AJSL.
    Context {C : Type} (AJSL : abstract_join_semilattice C).

    Instance ajsl_laws :
      @abstract_join_semilattice_laws C (ad AJSL)
        (ajsl_join AJSL) (ajsl_equiv AJSL).
    Proof.
      refine {| ajsl_ad_laws := _ |}.
      - move=> a1 a2 Heq.
        have [Hl Hr] := ajsl_equiv_compat (A:=AJSL) a1 a2 Heq.
        split; by right.
      - move=> a1 a2. right. exact: ajsl_join_compat_l.
      - move=> a1 a2. right. exact: ajsl_join_compat_r.
    Qed.

    Definition ajsl : abstract_join_semilattice C :=
      BuildAbstractJoinSemilattice (ad AJSL)
        (ajsl_join AJSL) (ajsl_equiv AJSL) ajsl_laws.
  End AJSL.

  (** *** [JoinIsLUB]-preserving variant.

      With the underlying join, [JoinIsLUB] fails. Counter-example in
      [IntervalUnbounded]: [(1,0)] is empty so [(1,0) ⊑_widened (2,3)],
      and [(2,3) ⊑_widened (2,3)] reflexively. Their underlying join
      is [(min 1 2, max 0 3) = (1,3)], non-empty and *not* [⊑[A] (2,3)]
      (since [2 ≰ 1]). The fix is to make γ-empty elements act as
      identities for join. This requires decidable γ-emptiness. *)
  Section AJSL_LUB.
    Context {C : Type} (AJSL : abstract_join_semilattice C).
    Context (is_empty_dec : forall a : AJSL, {is_empty AJSL a} + {~ is_empty AJSL a}).

    Definition join_lub_compat (a1 a2 : AJSL) : AJSL :=
      match is_empty_dec a1 with
      | left _ => a2
      | right _ =>
          match is_empty_dec a2 with
          | left _ => a1
          | right _ => ajsl_join AJSL a1 a2
          end
      end.

    Instance ajsl_lub_laws :
      @abstract_join_semilattice_laws C (ad AJSL)
        join_lub_compat (ajsl_equiv AJSL).
    Proof.
      refine {| ajsl_ad_laws := _ |}.
      - move=> a1 a2 Heq.
        have [Hl Hr] := ajsl_equiv_compat (A:=AJSL) a1 a2 Heq.
        split; by right.
      - move=> a1 a2. rewrite /join_lub_compat.
        case: (is_empty_dec a1) => H1; first by left.
        case: (is_empty_dec a2) => H2; first by right; reflexivity.
        right. exact: ajsl_join_compat_l.
      - move=> a1 a2. rewrite /join_lub_compat.
        case: (is_empty_dec a1) => H1; first by right; reflexivity.
        case: (is_empty_dec a2) => H2; first by left.
        right. exact: ajsl_join_compat_r.
    Qed.

    Definition ajsl_lub : abstract_join_semilattice C :=
      BuildAbstractJoinSemilattice (ad AJSL)
        join_lub_compat (ajsl_equiv AJSL) ajsl_lub_laws.

    Instance CollapsedBottom_JoinIsLUB `{HLUB:!JoinIsLUB AJSL} : JoinIsLUB ajsl_lub.
    Proof.
      move=> a1 a2 c H1 H2. rewrite /(_ ⊑[ajsl_lub] _) /= /is_included /join_lub_compat.
      case: (is_empty_dec a1) => He1; first by exact: H2.
      case: (is_empty_dec a2) => He2; first by exact: H1.
      case: H1 => [Hemp1 | Hle1]; first by contradiction.
      case: H2 => [Hemp2 | Hle2]; first by contradiction.
      right. exact: (join_lub (AJSL:=AJSL) a1 a2 c Hle1 Hle2).
    Qed.
  End AJSL_LUB.

  (** Lift a lattice: same join, meet, equiv, widened ⊑. *)
  Section AL.
    Context {C : Type} (AL : abstract_lattice C).

    Definition al : abstract_lattice C :=
      MkAbstractLattice (ajsl (al_ajsl AL)) (al_meet AL).
  End AL.

  (** [JoinIsLUB]-preserving lattice variant. *)
  Section AL_LUB.
    Context {C : Type} (AL : abstract_lattice C).
    Context (is_empty_dec : forall a : AL, {is_empty AL a} + {~ is_empty AL a}).

    Definition al_lub : abstract_lattice C :=
      MkAbstractLattice (ajsl_lub (al_ajsl AL) is_empty_dec) (al_meet AL).
  End AL_LUB.

End CollapsedBottom.


(** ** Subset types. *)
Module Subset.

  Section Abs.
    Context {C : Type} (A: abstraction C) (P: A -> Prop).
    
    Definition gamma (a: {a: A | P a}) :=
      let (a, _) := a in γ[A] a.

    Definition abs : abstraction C :=
      BuildAbstraction gamma.

    (* Definition subset_ad_to_whole (a:abs) := *)
    (*   BuildAbstraction  (γ[A]). *)

    
  End Abs.
  Global Hint Unfold gamma : unfold_gamma.

  (* Coercion subset_abs_to_whole {C} {ad P} (Abs:(abs ad P)) : abstraction C := ad. *)

  Section AD.
    Context {C : Type} (A: abstract_domain C) (P: A -> Prop).

    Definition is_included (a1 a2: {a: A | P a}) : Prop :=
      let (a1, _) := a1 in
      let (a2, _) := a2 in
      a1 ⊑[A] a2.
    
    Definition laws : abstract_domain_laws (γ[abs A P] ) is_included.
    Proof.
      refine {| ad_sqsubseteq_preorder := _ |}.
      (* Order-preservation. *)
      { to_set. move=> [a1 p1] [a2 p2]. rewrite /is_included.
        simpl. apply order_preserving. }
      Unshelve.
      (* PreOrder. *)
      split.
      + move=> [a p] //=. reflexivity.
      + move=> [x px] [y py] [z pz] Hxy Hyz. cbv in *. by transitivity y.
    Qed.

    Definition ad : abstract_domain C :=
      BuildAbstractDomain (γ[abs A P] ) is_included laws.

    (** ExactOrder is inherited unchanged: order and γ are unchanged. *)
    Instance Subset_ExactOrder `{!ExactOrder A} : ExactOrder ad.
    Proof.
      move=> [a1 p1] [a2 p2]. exact: (exact_order (A:=A) a1 a2).
    Qed.

    (** TODO: state the Galois connection for [Subset]. Some best abstractions of
        a set S may cease to exist, because they do not satisfy P; but those that
        do satisfy P remain best abstractions. *)
  End AD.

  (** *** Abstract join semilattice on a subset.

      Given an [abstract_join_semilattice A] and a predicate [P] that
      is closed under join, the subset [{a | P a}] inherits the
      join-semilattice structure with the same join. *)
  Section AJSL.
    Context {C : Type} (AJSL : abstract_join_semilattice C) (P : AJSL -> Prop).
    Context (Hjoin_closure :
      forall a1 a2 : AJSL, P a1 -> P a2 -> P (ajsl_join AJSL a1 a2)).

    Definition join (a1 a2 : { a : AJSL | P a }) : { a : AJSL | P a } :=
      exist _ (ajsl_join AJSL (`a1) (`a2))
        (Hjoin_closure (`a1) (`a2) (proj2_sig a1) (proj2_sig a2)).

    Definition equiv (a1 a2 : { a : AJSL | P a }) : Prop :=
      ajsl_equiv AJSL (`a1) (`a2).

    Instance ajsl_laws :
      @abstract_join_semilattice_laws C (ad AJSL P) join equiv.
    Proof.
      refine {| ajsl_ad_laws := _ |}.
      - move=> [a1 p1] [a2 p2] /=. exact: ajsl_equiv_compat.
      - move=> [a1 p1] [a2 p2] /=. exact: ajsl_join_compat_l.
      - move=> [a1 p1] [a2 p2] /=. exact: ajsl_join_compat_r.
    Qed.

    Definition ajsl : abstract_join_semilattice C :=
      BuildAbstractJoinSemilattice (ad AJSL P) join equiv ajsl_laws.

    (** JoinIsLUB is inherited: join and order are inherited unchanged. *)
    Instance Subset_JoinIsLUB `{HLUB:!JoinIsLUB AJSL} : JoinIsLUB ajsl.
    Proof.
      move=> [a1 p1] [a2 p2] [c pc]. exact: (join_lub (AJSL:=AJSL) a1 a2 c).
    Qed.
  End AJSL.

  (** *** Abstract lattice on a subset.

      For [abstract_lattice], we additionally need a way to project
      results of [meet] into the subset (since meet may produce
      elements outside [P]). The caller supplies a [norm] function;
      no laws are required on [meet]. *)
  Section AL.
    Context {C : Type} (AL : abstract_lattice C) (P : AL -> Prop).
    Context (Hjoin_closure :
              forall a1 a2 : AL, P a1 -> P a2 -> P (ajsl_join AL a1 a2)).
    Context (Hmeet_closure :
              forall a1 a2 : AL, P a1 -> P a2 -> P (al_meet AL a1 a2)).

    Definition meet (a1 a2 : { a : AL | P a }) : { a : AL | P a } :=
      exist _ (al_meet AL (`a1) (`a2))
        (Hmeet_closure (`a1) (`a2) (proj2_sig a1) (proj2_sig a2)).

    Definition al : abstract_lattice C :=
      MkAbstractLattice (ajsl (al_ajsl AL) P Hjoin_closure) meet.
  End AL.
End Subset.

(** NonEmpty is a particular property requiring that the abstract
elements concretize to non-empty sets. *)
Module NonEmpty.
  Include Subset.

  (** The defining predicate of this module: [a] concretises to a
      non-empty set. The abstract [P]/[HP] interface in [Section AD]
      below is just this at [P := pred A] with [HP := fun _ => iff_refl _]. *)
  Definition pred {C : Type} (A : abstraction C) (a : A) : Prop :=
    exists c, c ∈ γ[A] a.

  Section AD.
    Context {C : Type} (A: abstract_domain C) (P: A -> Prop).
    (** If P is equivalent to non-empty concretization, and fA is a
        sound binary overapproximation of a total function fC, then fA
        preserves non-emptiness. *)
    Lemma nonempty_lift_binary_sound
      (HP: forall a, P a <-> exists c, c ∈ γ[A] a)
      (fA: A -> A -> A) (fC: C -> C -> C)
      {Hsound: binary_overapproximation A A A fA (collecting_binary_forward fC)}
      a1 a2 (H1: P a1) (H2: P a2): P (fA a1 a2).
    Proof.
      have [c1 H11] := (HP a1).1 H1.
      have [c2 H22] := (HP a2).1 H2.
      apply <- HP.
      by exists (fC c1 c2); apply Hsound; unfold_set; exists c1, c2.
    Qed.

    (** Lifts a sound total binary operation on A to the subset type {a | P a}. *)
    Definition nonempty_lift_total_binary
      (HP: forall a, P a <-> exists c, c ∈ γ[A] a)
      (fA: A -> A -> A) (fC: C -> C -> C)
      {Hsound: binary_overapproximation A A A fA (collecting_binary_forward fC)}
      (i1 i2: {a: A | P a}): {a: A | P a}.
    Proof.
      refine (exist _ (fA (`i1) (`i2)) _).
      abstract (
          move: i1 => [i1 Hi1]; move: i2 => [i2 Hi2];
          by apply: (nonempty_lift_binary_sound HP)).
    Defined.
  End AD.

End NonEmpty.

(** ** MaximallyReducedSubset: restrict to maximally-reduced elements.

    A specialization of [Subset] whose predicate is [MaximallyReduced].
    On this carrier the abstract order coincides with γ-inclusion: if
    [a1] is maximally reduced and [γ a1 ⊆ γ a2], then [a2]
    over-approximates [γ a1], so by optimality of [a1] we get
    [a1 ⊑[A] a2]. Hence [ExactOrder] holds unconditionally. *)
Module MaximallyReducedSubset.

  Section AD.
    Context {C : Type} (A : abstract_domain C).

    Definition pred (a : A) : Prop := MaximallyReduced a.

    Definition abs : abstraction C := Subset.abs A pred.
    Definition ad : abstract_domain C := Subset.ad A pred.

    Global Instance MaximallyReducedSubset_ExactOrder : ExactOrder ad.
    Proof.
      move=> [a1 H1] [a2 H2]. split.
      - exact: (sound_order (A:=ad)).
      - move=> Hsub. exact: (best_abstraction_is_optimal (S:=γ[A] a1) a2 Hsub).
    Qed.
  End AD.

  (** Join-closure: if [A] has [JoinIsLUB], then [MaximallyReduced] is
      closed under join. Direct corollary of [join_is_lub_maximally_reduced]
      via [is_alpha_iff_best_abstraction]. *)
  Section AJSL.
    Context {C : Type} (AJSL : abstract_join_semilattice C) `{!JoinIsLUB AJSL}.

    Lemma join_closure (a1 a2 : AJSL) :
      pred AJSL a1 -> pred AJSL a2 -> pred AJSL (ajsl_join AJSL a1 a2).
    Proof using JoinIsLUB0.
      rewrite /pred /MaximallyReduced -!is_alpha_iff_best_abstraction.
      exact: join_is_lub_maximally_reduced.
    Qed.

    Definition ajsl : abstract_join_semilattice C :=
      Subset.ajsl AJSL (pred AJSL) join_closure.

    Instance MaximallyReducedSubset_JoinIsLUB : JoinIsLUB ajsl.
    Proof. exact: Subset.Subset_JoinIsLUB. Qed.
  End AJSL.

End MaximallyReducedSubset.

(** ** CanonicalBottom: canonical γ-empty representatives.

    Given an abstract domain [A] and boolean test [is_bottomb : A ->
    bool] characterising the accepted γ-empty (bottom) representatives
    — with [is_bottomb a -> γ a ≡ ∅] — [CanonicalBottom] restricts the
    carrier to [{ a : A | ¬ γ-empty a ∨ is_bottomb a }]. The classic
    single-element case is recovered by passing a boolean equality
    test [fun a => eqb a bottom].

    The order is widened so every [is_bottomb] element is a
    [⊑]-minimum and redefine join to be bottom-absorbing, so
    [JoinIsLUB] lifts from the underlying domain. If you don't want
    order-widening, use Subset; if you want to widen the order without
    restricting the carrier, see [CollapsedBottom] instead. *)
Module CanonicalBottom.

  Section Pred.
    Context {C : Type} (A : abstract_domain C) (is_bottomb : A -> bool).

    (** "Non-empty or canonical bottom". *)
    Definition pred (a : A) : Prop :=
      NonEmpty.pred A a \/ is_bottomb a.

  End Pred.

  (** *** Order-widening, [JoinIsLUB]-preserving variants.

      These variants apply the same principle as [CollapsedBottom]:
      since they widen the abstract order so that any bottom element
      becomes the minimum, the join must be redefined accordingly so
      that [bot ⊔ x = x]. This preserves [JoinIsLUB]. *)
  Section AD.
    Context {C : Type} (A : abstract_domain C) (is_bottomb : A -> bool)
            (HBot_empty : forall a, is_bottomb a -> γ[A] a ⊆⊇ ∅).

    Local Notation P := (pred A is_bottomb).
    Local Notation carrier := { a : A | P a }.

    Definition is_included (a1 a2 : carrier) : Prop :=
      is_bottomb (`a1) \/ `a1 ⊑[A] `a2.

    (** On the [pred] carrier, [γ a ≡ ∅] forces [is_bottomb a]: the
        non-empty disjunct of [pred] would supply a witness. *)
    Lemma pred_empty_is_bot (a : A) : P a -> γ[A] a ⊆⊇ ∅ -> is_bottomb a.
    Proof.
      move=> [[c Hc] | HB] Hemp.
      - exfalso. exact: (proj1 Hemp c Hc).
      - exact: HB.
    Qed.

    (** A [pred] element that is not [is_bottomb] is non-empty: the
        bottom disjunct of [pred] is ruled out. *)
    Lemma pred_not_bot_nonempty (a : A) :
      P a -> is_bottomb a <> true -> NonEmpty.pred A a.
    Proof. move=> [H | Hb] Hne; [exact: H | by case: (Hne Hb)]. Qed.

    Lemma laws :
      abstract_domain_laws (abs_gamma (Subset.abs A P)) is_included.
    Proof using HBot_empty.
      refine {| ad_sqsubseteq_preorder := _ |}.
      (* Soundness. *)
      { move=> [a1 P1] [a2 P2] H c Hc.
        case: H => [HB1 | Hle] /=.
        - simpl in HB1, Hc.
          exfalso. exact: (proj1 (HBot_empty a1 HB1) c Hc).
        - exact: (ad_γ_order_preserving a1 a2 Hle c Hc). }
      Unshelve.
      split.
      - move=> a. right. reflexivity.
      - move=> [a1 P1] [a2 P2] [a3 P3] H12 H23.
        case: H12 => [HB|H12]; first by left.
        case: H23 => [HB|H23].
        + left.
          have Hempty1 : γ[A] a1 ⊆⊇ ∅.
          { split=> c Hc; last by [].
            have Hc2 : c ∈ γ[A] a2 by exact: (ad_γ_order_preserving a1 a2 H12 c Hc).
            exact: (proj1 (HBot_empty a2 HB) c Hc2). }
          exact: (pred_empty_is_bot a1 P1 Hempty1).
        + right. simpl in H12, H23. by transitivity a2.
    Qed.

    Definition ad : abstract_domain C :=
      BuildAbstractDomain (abs_gamma (Subset.abs A P)) is_included laws.
  End AD.

  Section AJSL.
    Context {C : Type} (AJSL : abstract_join_semilattice C) (is_bottomb : AJSL -> bool)
            (HBot_empty : forall a, is_bottomb a -> γ[AJSL] a ⊆⊇ ∅).
    (** Join-closure is only required on *non-empty* inputs: [bot_join]
        is bottom-absorbing, so it only ever applies the underlying join
        when neither input is [is_bottomb] (hence both non-empty). The
        stronger "closed on all [pred] inputs" statement would be false
        whenever [is_bottomb] admits several bottoms that join to a
        non-bottom γ-empty element (e.g. interval-bottom in a reduced
        product). *)
    Context (Hjoin_closure :
      forall a1 a2 : AJSL,
        NonEmpty.pred AJSL a1 -> NonEmpty.pred AJSL a2 ->
        pred AJSL is_bottomb (ajsl_join AJSL a1 a2)).

    Local Notation P := (pred AJSL is_bottomb).
    Local Notation carrier := { a : AJSL | P a }.

    (** Raw bottom-absorbing join over the underlying carrier — the
        executable core (extraction target). [bot_join] wraps it with the
        subset-type invariant proof ([join_raw_pred]). [bot ⊔ x = x],
        [x ⊔ bot = x], else underlying join; [is_bottomb] is the dispatch
        test. *)
    Definition join_raw (a1 a2 : AJSL) : AJSL :=
      if is_bottomb a1 then a2
      else if is_bottomb a2 then a1
      else ajsl_join AJSL a1 a2.

    (** [join_raw] preserves the [pred] invariant. In the fall-through
        branch both inputs are not [is_bottomb], so [pred_not_bot_nonempty]
        turns their [pred] proofs into the non-emptiness [Hjoin_closure]
        needs. *)
    Lemma join_raw_pred (a1 a2 : carrier) : P (join_raw (`a1) (`a2)).
    Proof using AJSL C Hjoin_closure is_bottomb.
      rewrite /join_raw.
      case E1: (is_bottomb (`a1)); first exact: (proj2_sig a2).
      case E2: (is_bottomb (`a2)); first exact: (proj2_sig a1).
      apply: Hjoin_closure; apply: pred_not_bot_nonempty;
        [exact: (proj2_sig a1) | by rewrite E1
        | exact: (proj2_sig a2) | by rewrite E2].
    Qed.

    Definition bot_join (a1 a2 : carrier) : carrier :=
      exist _ (join_raw (`a1) (`a2)) (join_raw_pred a1 a2).

    Lemma bot_join_raw (a1 a2 : carrier) :
      proj1_sig (bot_join a1 a2) = join_raw (`a1) (`a2).
    Proof. reflexivity. Qed.

    Definition equiv (a1 a2 : carrier) : Prop :=
      ajsl_equiv AJSL (`a1) (`a2).

    Instance ajsl_laws :
      @abstract_join_semilattice_laws C (ad AJSL is_bottomb HBot_empty)
        bot_join equiv.
    Proof.
      refine {| ajsl_ad_laws := _ |}.
      - move=> [a1 P1] [a2 P2] /= Heq.
        have [Hl Hr] := ajsl_equiv_compat (A:=AJSL) a1 a2 Heq.
        split; by right.
      - move=> [a1 P1] [a2 P2]. rewrite /(_ ⊑[_] _) /= /is_included /bot_join /join_raw /=.
        case: (is_bottomb a1) => /=; first by left.
        case: (is_bottomb a2) => /=; first by right; reflexivity.
        right. exact: ajsl_join_compat_l.
      - move=> [a1 P1] [a2 P2]. rewrite /(_ ⊑[_] _) /= /is_included /bot_join /join_raw /=.
        case: (is_bottomb a1) => /=; first by right; reflexivity.
        case: (is_bottomb a2) => /=; first by left.
        right. exact: ajsl_join_compat_r.
    Qed.

    Definition ajsl : abstract_join_semilattice C :=
      BuildAbstractJoinSemilattice (ad AJSL is_bottomb HBot_empty)
        bot_join equiv ajsl_laws.

    Global Instance CanonicalBottom_JoinIsLUB `{HLUB:!JoinIsLUB AJSL} : JoinIsLUB ajsl.
    Proof.
      move=> [a1 P1] [a2 P2] [c Pc] H1 H2.
      rewrite /(_ ⊑[ajsl] _) /= /is_included /bot_join /join_raw /=.
      case E1: (is_bottomb a1); first exact: H2.
      case E2: (is_bottomb a2); first exact: H1.
      have Hle1 : a1 ⊑[AJSL] c.
      { move: H1. rewrite /(_ ⊑[ajsl] _) /= /is_included /= => -[Hb1|//].
        by rewrite E1 in Hb1. }
      have Hle2 : a2 ⊑[AJSL] c.
      { move: H2. rewrite /(_ ⊑[ajsl] _) /= /is_included /= => -[Hb2|//].
        by rewrite E2 in Hb2. }
      rewrite /is_included /=. right.
      exact: (join_lub (AJSL:=AJSL) a1 a2 c Hle1 Hle2).
    Qed.
  End AJSL.

  Section AL.
    Context {C : Type} (AL : abstract_lattice C) (is_bottomb : AL -> bool)
            (HBot_empty : forall a, is_bottomb a -> γ[AL] a ⊆⊇ ∅).
    Context (Hjoin_closure :
      forall a1 a2 : AL,
        NonEmpty.pred AL a1 -> NonEmpty.pred AL a2 ->
        pred AL is_bottomb (ajsl_join AL a1 a2)).
    Context (pred_dec : AL -> bool).
    Context (Hpred_dec : forall a, reflect (pred AL is_bottomb a) (pred_dec a)).
    Context (bot0 : AL) (Hbot0 : is_bottomb bot0).

    Definition meet (a1 a2 : { a : AL | pred AL is_bottomb a })
      : { a : AL | pred AL is_bottomb a }.
    Proof using AL C is_bottomb bot0 Hbot0 pred_dec Hpred_dec Hjoin_closure.
      set m := al_meet AL (`a1) (`a2).
      case: (Hpred_dec m) => [Hp|_].
      - exact (exist _ m Hp).
      - exists bot0. rewrite /pred/NonEmpty.pred. by right.
    Defined.

    Definition al : abstract_lattice C :=
      MkAbstractLattice (ajsl AL is_bottomb HBot_empty Hjoin_closure) meet.
  End AL.

End CanonicalBottom.

(** ** Conjunction of abstractions.

    A pair (A,B) when both are abstractions of C represent a
    conjunction of properties over C. The difficulty here is
    maintaining precision: to obtain the best precision in the
    abstract, one must perform a reduction between the two properties,
    when there are some inter-dependencies between them. *)
Module Conjunction.

  (** *** Conjunction of abstractions *)
  Section Abs.
    Context {C : Type} (A B: abstraction C).

    Definition gamma (p:A * B) := let (a,b) := p in γ[A] a ∩ γ[B] b.
    
    Definition abs : abstraction C :=
      BuildAbstraction gamma.

    Global Instance gammaP inA inB:
      (forall (x:C) a, AutoReflect(x ∈ γ[A] a)(inA a x)) ->
      (forall (x:C) b, AutoReflect(x ∈ γ[B] b)(inB b x)) ->
      (forall x ab, AutoReflect(x ∈ γ[abs] ab)(let (a,b) := ab in inA a x && inB b x)).
    Proof.
      move=> HA HB x [a b].
      by apply: (iffP (andPP (HA x a) (HB x b))).
    Qed.

    Lemma gammaE c aa ab:
      c ∈ γ[abs] (aa,ab) <-> c ∈ γ[A] aa /\ c ∈ γ[B] ab.
    Proof.
      firstorder.
    Qed.

  End Abs.
  Global Hint Unfold gamma : unfold_gamma.

  (** *** Conjunction of abstract domains. *)
  Section AD.
    Context {C : Type} (A B: abstract_domain C).
    
    Definition is_included := fun (ab1 ab2:abs A B) =>
      let (a1,b1) := ab1 in
      let (a2,b2) := ab2 in
      a1 ⊑[A] a2 /\ b1 ⊑[B] b2.

    Definition laws : abstract_domain_laws (γ[abs A B] ) is_included.
    Proof.
      pose(HA:= ad_mixin A). pose(HB:= ad_mixin B).
      have PA: PreOrder (⊑[A]). by apply _.
      have PB: PreOrder (⊑[B]). by apply _.
      have OA: OrderPreserving (γ[A] ) (⊑[A]) (⊆). apply: ad_γ_order_preserving.
      have OB: OrderPreserving (γ[B] ) (⊑[B]) (⊆). apply: ad_γ_order_preserving.
      refine {| ad_γ_order_preserving := _ |}.
      {  to_set. move=> ab1 ab2.
         destruct ab1 as (a1,b1). destruct ab2 as (a2,b2).
         move=> [HleA HleB]. firstorder. }
      Unshelve.
      (* PreOrder. *)
      split.
        + move=> [a b]. unfold is_included; split; reflexivity.
        + move=>  [ax bx] [ay _by] [az bz]. 
          rewrite /is_included.
          move=> [Hxya Hxyb] [Hyza Hyzb].
          split; [transitivity ay|transitivity _by]; assumption.
    Qed.
        
    Definition ad : abstract_domain C :=
      BuildAbstractDomain (γ[abs A B] ) is_included laws.

    Global Instance is_includedP is_includedbA is_includedbB a1 a2 b1 b2:
      (AutoReflect(a1 ⊑[A] a2)(is_includedbA a1 a2)) ->
      (AutoReflect(b1 ⊑[B] b2)(is_includedbB b1 b2)) ->
      (AutoReflect((a1,b1) ⊑[ad] (a2,b2))(is_includedbA a1 a2 && is_includedbB b1 b2)).
    Proof.
      move=> HA HB. apply _.
    Qed.

    (** An interesting fact is this: if both a and b are the most
        precise (i.e., with the concrete order ⊑γ) abstraction of S,
        then (a,b) is the most precise abstraction of S. However, if
        (a,b) is the most precise abstraction of S, this does not
        imply that a and b are the most precise. For instance,
        ([1-5],"multiple of 3") has the most precise concretization
        ({3}), but [1-5] does not have the most precise
        concretization. Indeed, the goal of the reduced product is to
        solve this problem.

        What is interesting is that this property holds in the
        abstract: [(a,b)] is the best abstraction of [S] iff both [a]
        and [b] are best abstractions of [S]. The next lemma states
        this directly for [IsAlpha], and the [galoisW] / [galois]
        instances below are immediate corollaries. This is one
        situation where the abstract objects have better properties
        than concrete ones, and it makes it much simpler to reason
        about maximally precise reduced products. *)
    (** Compositionality phrased in terms of [BestAbstraction]. The
        two components of the pair are split apart structurally:
        [BestAbstraction] separates soundness ([Overapproximates])
        from optimality, and the soundness of [(a, b)] for [S] *is*
        the conjunction of the per-component soundnesses (since
        [γ[ad] (a, b) = γ[A] a ∩ γ[B] b]). The optimality side then
        only needs the standard "fill in the other component"
        argument. *)
    Lemma best_abstraction_pair_iff (a : A) (b : B) (S : ℘ C) :
      BestAbstraction (A := ad) (a, b) S <->
      BestAbstraction (A := A) a S /\ BestAbstraction (A := B) b S.
    Proof.
      split.
      - (* BestAbstraction (a, b) S -> BestAbstraction a S /\ BestAbstraction b S *)
        move=> [Hsound Hopt]. split.
        + split.
          * (* Overapproximates a S — direct projection. *)
            move=> c Hc. have /= [? _] := Hsound c Hc; assumption.
          * (* a is optimal: combine S ⊆ γ a' with S ⊆ γ b (from
               Hsound) to apply joint optimality at (a', b). *)
            move=> a' Ha'.
            have HSa'b : S ⊆ γ[ad] (a', b).
            { move=> c Hc /=. split.
              - exact: Ha' Hc.
              - by have /= [_ ?] := Hsound c Hc. }
            have [Hla _] := Hopt (a', b) HSa'b. exact: Hla.
        + split.
          (* Overapproximates b S — same proof. *)
          * move=> c Hc. have /= [_ ?] := Hsound c Hc; assumption.
          * move=> b' Hb'.
            have HSab' : S ⊆ γ[ad] (a, b').
            { move=> c Hc /=. split.
              - by have /= [? _] := Hsound c Hc.
              - exact: Hb' Hc. }
            have [_ Hlb] := Hopt (a, b') HSab'. exact: Hlb.
      - (* BestAbstraction a S /\ BestAbstraction b S -> BestAbstraction (a, b) S *)
        move=> [[HSa HoptA] [HSb HoptB]]. split.
        + move=> c Hc /=.  split; [exact: HSa Hc | exact: HSb Hc].
        + move=> [a' b'] Hab'. split.
          * apply: HoptA => c Hc.
            have /= [? _] := Hab' c Hc; assumption.
          * apply: HoptB => c Hc.
            have /= [_ ?] := Hab' c Hc; assumption.
    Qed.

    Lemma most_precise_pair (a : A) (b : B) (S : ℘ C) :
      MostPrecise (A := A) a S /\ MostPrecise (A := B) b S      
      -> MostPrecise (A := ad) (a, b) S.
    Proof.
      move => [[HSoundA HOptA] [HSoundB HOptB]]. split.
      - to_set in *. unfold_set in *. firstorder.
      - to_set in *. move => [a' b'] Hab'. simpl in Hab'. transitivity ((γ[ ad] ) (a', b)).
        + simpl. suffices: (ad_gamma A a ⊆ ad_gamma A a') by firstorder.
          apply HOptA. firstorder.
        + simpl. suffices: (ad_gamma B b ⊆ ad_gamma B b') by firstorder.
          apply HOptB.  firstorder.          
    Qed.



    

    (** Same statement under [IsAlpha], obtained by transport
        through [is_alpha_iff_best_abstraction]. This is the form
        the [galoisW] / [galois] instances below consume. *)
    Lemma is_alpha_pair_iff (a : A) (b : B) (S : ℘ C) :
      IsAlpha (A := ad) (a, b) S <->
      IsAlpha (A := A) a S /\ IsAlpha (A := B) b S.
    Proof.
      rewrite !is_alpha_iff_best_abstraction.
      exact: best_abstraction_pair_iff.
    Qed.

    Instance galoisW: (WeakAlphaRelation A) -> (WeakAlphaRelation B) -> WeakAlphaRelation (ad).
    Proof.
      move=> [is_αA His_αA Aproper] [is_αB His_αB Bproper].
      refine {| weak_α_relation :=
                 fun (ab: ad) S => let (a,b) := ab in is_αA a S /\ is_αB b S |}.
      - move=> [a b] S [Ha Hb].
        apply (proj2 (is_alpha_pair_iff a b S)).
        split; [exact: His_αA Ha | exact: His_αB Hb].
      - move=> [a b] SA SB HAB. setoid_rewrite HAB; reflexivity.
    Defined.

    Instance galois: (StrongAlphaRelation A) -> (StrongAlphaRelation B) -> StrongAlphaRelation (ad).
    Proof.
      move=> [is_αA His_αA] [is_αB His_αB].
      refine {| strong_α_relation :=
                 fun (ab: ad) S => let (a,b) := ab in is_αA a S /\ is_αB b S |}.
      move=> [a b] S.
      rewrite is_alpha_pair_iff (His_αA a S) (His_αB b S).
      reflexivity.
    Defined.
  End AD.

  (** *** Abstract join semilattice (unreduced product). *)
  Section AJSL.
    Context {C : Type} (AJSLA AJSLB: abstract_join_semilattice C).

    Let adA : abstract_domain C := AJSLA.
    Let adB : abstract_domain C := AJSLB.

    Definition join (ab1 ab2: AJSLA * AJSLB) : AJSLA * AJSLB :=
      let (a1,b1) := ab1 in
      let (a2,b2) := ab2 in
      (ajsl_join AJSLA a1 a2, ajsl_join AJSLB b1 b2).

    Definition equiv (ab1 ab2: AJSLA * AJSLB) : Prop :=
      let (a1,b1) := ab1 in
      let (a2,b2) := ab2 in
      ajsl_equiv AJSLA a1 a2 /\ ajsl_equiv AJSLB b1 b2.

    Instance ajsl_laws :
      @abstract_join_semilattice_laws C (ad adA adB) join equiv.
    Proof.
      refine {| ajsl_ad_laws := _ |}.
      - move=> [a1 b1] [a2 b2] [Ha Hb].
        have [? ?] := ajsl_equiv_compat _ _ Ha.
        have [? ?] := ajsl_equiv_compat _ _ Hb.
        split; split; assumption.
      - move=> [a1 b1] [a2 b2]; split.
        + exact (ajsl_join_compat_l a1 a2).
        + exact (ajsl_join_compat_l b1 b2).
      - move=> [a1 b1] [a2 b2]; split.
        + exact (ajsl_join_compat_r a1 a2).
        + exact (ajsl_join_compat_r b1 b2).
    Qed.

    Definition ajsl : abstract_join_semilattice C :=
      BuildAbstractJoinSemilattice (ad adA adB) join equiv ajsl_laws.

    Instance Conjunction_JoinIsLUB `{HLUB_A:!JoinIsLUB AJSLA} `{HLUB_B:!JoinIsLUB AJSLB} : JoinIsLUB ajsl.
    Proof.
      move=> [a1 b1] [a2 b2] [c1 c2] [Ha1 Hb1] [Ha2 Hb2]; split.
      - exact (join_lub a1 a2 c1 Ha1 Ha2).
      - exact (join_lub b1 b2 c2 Hb1 Hb2).
    Qed.
  End AJSL.

  (** *** Abstract lattice (unreduced product). *)
  Section AL.
    Context {C : Type} (ALA ALB: abstract_lattice C).

    Definition meet (ab1 ab2: ALA * ALB) : ALA * ALB :=
      let (a1,b1) := ab1 in
      let (a2,b2) := ab2 in
      (al_meet ALA a1 a2, al_meet ALB b1 b2).

    Definition al : abstract_lattice C :=
      MkAbstractLattice (ajsl (al_ajsl ALA) (al_ajsl ALB)) meet.
  End AL.

End Conjunction.

(** Make [unfold_gamma] see through the combinator domain/semilattice
    constructors. Without these, [autounfold with unfold_gamma] stops at
    e.g. [ad_gamma (CollapsedBottom.ad A)] because the [.ad]/[.ajsl]
    definitions are opaque to it, so it never reaches the underlying
    [γ]. The leaf [gamma] functions and the projections/coercions are
    already registered (above and in [Abstraction.v]); these complete
    the chain. *)
Global Hint Unfold
  WithTop.abs WithTop.ad WithTop.ajsl WithTop.al
  WithBottom.abs WithBottom.ad
  CollapsedBottom.ad CollapsedBottom.ajsl CollapsedBottom.ajsl_lub
  CollapsedBottom.al CollapsedBottom.al_lub
  Subset.abs Subset.ad Subset.ajsl Subset.al
  MaximallyReducedSubset.abs MaximallyReducedSubset.ad MaximallyReducedSubset.ajsl
  CanonicalBottom.ad CanonicalBottom.ajsl CanonicalBottom.al
  Conjunction.abs Conjunction.ad Conjunction.ajsl Conjunction.al
  : unfold_gamma.
