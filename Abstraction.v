(** * Options *)

(** Allow async proof-checking of sections. *)
#[export] Set Default Proof Using "Type".

(** Require the proper use of bullets and curly braces.

    Note: disabled as this is bothersome during proofs; but we should
    check it on commited code.  *)
(** #[export] Set Default Goal Selector "!". *)

Generalizable All Variables.
Set Primitive Projections.

From Stdlib Require Export Setoid.
From Stdlib Require Export Classes.Morphisms.
From Stdlib Require Import Utf8.

(** We use ssreflect for the more predictable proof scripts, good way
    of working with lots of case splits; because it allows unfolding
    notations with rewrite /(_ ⊆ _), etc. *)
Require Import ssreflect.
Require Export base.

Open Scope rocq_bottom_scope.

(** *** Conventions

    We essentially follow the mathcomp style:

    - we suffix by b for boolean versions;
    - we suffix by P for reflect predicates;
    - we suffix by E for elimination (definition) lemmas.  *)



(** * Hierarchy of abstractions.

 This file defines our hierarchy of abstractions:

    - An [abstraction C] is a set with a concretization to a propset
      C;

    - An [abstract_domain C] adds an ordering between abstract
      elements, compatible with an ordering in the concrete.

    - An [abstraction_setoid C] adds an equivalence relation (Leibniz
      equality when possible, but this is not possible for subset
      types) on elements of A

    - An [abstract_lattice] adds the lattice operations: join and meet
      (see AbstractLattice.v). Computable inclusion tests are provided
      per-domain, as [is_included] in the [ABSTRACT_DOMAIN] signature.

Further different extensions of the hierarchy include
[value_based_abstract_domain] (which adds join with renaming), and
[aadt] (which adds anti-unification). *)

(** *** Encoding the hierarchy.

Our hierarchy follows the packed class approach [Garillot et al,
Packaging Mathematical Structures, 2009], but we also use the
type-classes based unbundled approach [Spitters&van der Weeger, Type
Classes for Mathematics in Type Theory, 2011]:

- We create "mixins" in the unbundled style, which are just a
  conjunction of properties on "operational type classes". These are
  suffixed by "laws" in this development.

- The hierarchy consists in packed records, that group together the
  carrier type, the operations, and the laws. We use coercions to
  represent the relations in the hierarchy.

Note that we define a new element in the hierarchy when we add a new
operator; additional properties, and derived operators, are encoded
only using typeclasses.

This style should allow:

- combining the flexibility and automation of typeclasses;

- to be explicit about the properties of our abstractions. Note that
  in particular, there may be several concretization and ordering
  relation on the same carrier type, so indexing on the type only
  would not work. We want to index based on an abstraction (a gamma
  function).

- avoid the exponential explosion of proof terms of the
  fully-unbundled approach, in particular when combining structures
  (as in reduced product), which we do a lot in abstract
  interpretation. *)

(** * Tactics and levels of reasoning.

We define three possible levels of reasoning for our abstract
interpretation proofs, from high-level to low level:

- The abstract level (e.g.: a1 ⊑γ a2), using type classes like
  "Overapproximates" and order relations like ⊆γ. This is where we
  state our proofs.

- The set-algebraic level (e.g. γ a1 ⊆ γ a2). We use the to_set tactic
  and the rewrite/unfold database [to_set] to transform proofs into
  this level. There, we can in particular use rewriting for the ≡
  relation, and transitivity of ⊆.

- The element-wise/logical level (e.g. ∀ c ∈ γ a1, c ∈ γ a2). We use
  unfold_set to get to this level. It is best for mathematical proofs
  about a particular abstraction.

In proofs, we try to postpone the need to go to a more concrete level
of reasoning, as this makes the intermediary proof state unreadable. *)


(** The to_set tactic and db changes the proof from abstract level to
the set-algebraic level. *)
Create HintDb to_set.


(* Note: we try rewriting first; in particular, maybe some forms can
be simplified in better way than what unfolding does. *)
Global Ltac to_set :=
  repeat (try autorewrite with to_set; autounfold with to_set).

Global Tactic Notation "to_set" "in" hyp(H) :=
  repeat (try autorewrite with to_set in H; autounfold with to_set in H).

Global Tactic Notation "to_set" "in" "*" :=
  repeat(try autorewrite with to_set in *; autounfold with to_set in * ).

(** The unfold_gamma tactic changes the proof to reason about the
    specific abstraction we are using.

    TODO: this does not work very well. What matters is to maximally unfold the
    first argument of the γ functions; we should probably replace occurrences of
    [x ∈ γ ...] by some [P x]. *)
Create HintDb unfold_gamma.

Global Ltac unfold_gamma :=
  autounfold with unfold_gamma(* ; *)
  (* autorewrite with unfold_gamma *).

Global Tactic Notation "unfold_gamma" "in" hyp(H) :=
  autounfold with unfold_gamma in H(* ; *)
  (* autorewrite with unfold_gamma in H *).

Global Tactic Notation "unfold_gamma" "in" "*" :=
  autounfold with unfold_gamma in *(* ; *)
  (* autorewrite with unfold_gamma in * *).

(** * Abstraction.  *)

(** An [abstraction C] is an abstract element that represents a set of
C. Note that there are no laws. We set up an automatic coercion from
an abstraction to its carrier set abs_car.

Note: this coercion is convenient in proofs, but because we pack the
type inside the record, extraction of code using this coercion create
a lot of obj.magic. We could use instead a semi-bundled version, where
both types are a parameter, to avoid this problem. For now, we make
sure to write extracted functions such that they do not use the
coercion (i.e. extracted functions directly operate on the underlying
object).  *)

Structure abstraction C :=
  BuildAbstraction {
      abs_car :> Type;
      abs_gamma: abs_car -> propset C;
    }.

Global Arguments BuildAbstraction {_} {_} _.
(* Build abstractions out of a gamma function. *)
Global Arguments abs_car {_} _ /.
Global Arguments abs_gamma {_} _ /.
Global Hint Unfold abs_gamma : unfold_gamma.

(** We use the [ abs ] notation when we want to be explicit about
    which abstraction is being used. Whenever there are multiple
    abstractions, this should be the case.

    Note: we want to be explicit most of the time; possibly we could
    remove the Gamma instance and be explicit all the time. *)
Global Notation "'γ[' A ']'" := (abs_gamma A) (at level 10) : rocq_bottom_scope.
(* Global Notation "(γ[ A ])" := (abs_gamma A) (only parsing) : rocq_bottom_scope. *)
(* Global Notation "(.∈γ[ A ])" := (fun c a =>  c ∈ abs_gamma A a) (at level 10, A at level 0) : rocq_bottom_scope. *)


(** Some operational classes defining common notations.  Note that
    gamma depends on an abstraction, not on a type, as there may
    be several abstractions for the same type. *)
Class Gamma `(A: abstraction C) := γ: (abs_car A) -> propset C.
Arguments γ {C A} {Gamma} / _.

(** This is a more performant version of Existing Instance abs_gamma.

    Note 1: we don't really need this here, and we don't want to be
    implicit about γ everywhere, so we eventually don't define
    it. Possibly this could be used in files where gamma is not
    ambiguous. *)
(* Hint Extern 0 (Gamma _ _) => refine (abs_gamma _); shelve : typeclass_instances. *)

(** ** Concrete order.

    From an abstraction, we can already order elements by comparing
    their concretization. This is the concrete ordering, that we
    represent using the symbol ⊑γ. The abstract ordering, ⊑, is a more
    precise notion, in that elements of equal precision may not be
    equal in the abstract; however, precision in the concrete is what
    is ultimately interesting. *)

(** Note: we could be using typeclasses and a rewriting rules as
follows, but it is simpler if sqsubseteqgamma is just a definition. *)
(** Because ⊑γ is a derived notion, it is simpler to avoid using an
"operational typeclasses" and just make it a definition that depends
on the abstraction. *)

Definition sqsubseteq_gamma `{Gamma C A} : relation A :=
  fun a1 a2 => γ a1 ⊆ γ a2.

(* Global Notation "(⊑γ)" := sqsubseteq_gamma. *)
Global Infix "⊑γ" := sqsubseteq_gamma (at level 70).
Global Notation "(⊑γ[ A ])" := (@sqsubseteq_gamma _ _ (γ[A])).
Global Notation "a1 ⊑γ[ A ] a2" := (@sqsubseteq_gamma _ _ (γ[A] ) a1 a2) (at level 70).

Lemma sqsubseteq_gammaE `(A:abstraction C) (a1 a2 : A) : (a1 ⊑γ[A] a2) = (γ[A] a1 ⊆ γ[A] a2).  
Proof. reflexivity. Qed. 
Global Hint Rewrite @sqsubseteq_gammaE: to_set.
Global Hint Unfold sqsubseteq_gamma: to_set.

Global Instance unfold_set_sqsubseteq_gamma `(A:abstraction C) (a1 a2 : A) :
  UnfoldSet (a1 ⊑γ[A] a2) (forall c : C, c ∈ γ[A] a1 → c ∈ γ[A] a2).
Proof. constructor. reflexivity. Qed.

(** The sqsubseteq_gamma relation derived in the context of our gamma
    abstraction Abs, is reflexive and transitive. *)
Global Instance sqsubseteq_gamma_preorder {C} `(A:abstraction C): PreOrder (⊑γ[A]).
Proof.
  constructor.
  - by move=> a.
  - move=> a b c Hab Hbc. to_set in *. by transitivity ( γ[A] b).
Qed.


(** Reduction theory is developed below, after [BestAbstraction] and
    related notions are introduced (see "Reductions"). *)


(** * OrderPreserving, OrderReflecting, OrderEmbedding.  *)

(** We use the following definitions from order theory, that will
    apply to the γ function. The minimal requirement is that γ is
    monotone/order-preserving; i.e., that the order is sound
    wrt. gamma. Some additional properties are possible when γ is
    order-embedding, i.e. the abstract order exactly corresponds to
    the concrete order. *)

Class OrderPreserving {A B:Type} (f:A -> B) lea  leb `{PreA:PreOrder A lea} `{PreB:PreOrder B leb} :=
  order_preserving: forall a1 a2:A, lea a1 a2 -> leb (f a1) (f a2).
Class OrderReflecting {A B:Type} (f:A -> B) lea leb `{PreA:PreOrder A lea} `{PreB:PreOrder B leb} :=
  order_reflecting: forall a1 a2:A, leb (f a1) (f a2) -> lea a1 a2.
Class OrderEmbedding {A B:Type} (f:A -> B) lea leb `{PreA:PreOrder A lea} `{PreB:PreOrder B leb} :=
  order_embedding: forall a1 a2:A, lea a1 a2 <-> leb (f a1) (f a2).

(* Note: using this typeclass can make Rocq hangs, and this does not suffice to fix it.
   Be careful when applying order_preserving / order_embedding directly.  *)
(* Global Hint Mode OrderPreserving - - ! ! ! ! ! : typeclass_instances. *)
(* Global Hint Mode OrderPreserving - - - ! ! - - : typeclass_instances. *)

Hint Unfold OrderPreserving OrderReflecting OrderEmbedding
  order_preserving order_reflecting order_embedding: to_set. 

Instance order_embedding_is_order_preserving `{H:OrderEmbedding A B f lea leb}: OrderPreserving f lea leb.
Proof. move=> a1 a2. by rewrite H. Qed.

Instance order_embedding_is_order_reflecting `{H:OrderEmbedding A B f lea leb}: OrderReflecting f lea leb.
Proof. move=> a1 a2. by rewrite -H. Qed.

(** * AbstractDomain: Abstractions with an abstract order. *)

(* TODO: Wrap inside a module, which will provide a namespace. This
   allows for uniform naming: AbstractDomain.carrier,
   AbstractDomain.gamma, AbstractDomain.laws,
   AbstractDomain.sqsubseteq, etc. *)


(** An abstract domain is a set with some equality and some abstract
      order, such that the equality and orders are compatible with
      gamma (equivalent elements have the same concretization, and
      abstract ordering implies concrete ordering). *)
Class abstract_domain_laws `{A:abstraction C} (gamma:A -> propset C) (sqsubseteq:A -> A -> Prop) :=
  {
    ad_sqsubseteq_preorder:> PreOrder sqsubseteq;    
    ad_γ_order_preserving:> OrderPreserving (PreA:=ad_sqsubseteq_preorder) gamma sqsubseteq (⊆);
  }.

Structure abstract_domain (C:Type) := 
  BuildAbstractDomain {
      ad_car :> Type;
      ad_gamma: ad_car -> propset C;
      (* ad_equiv: Equiv ad_car; *)
      ad_sqsubseteq: ad_car -> ad_car -> Prop;
      ad_mixin: @abstract_domain_laws C (BuildAbstraction ad_gamma) ad_gamma ad_sqsubseteq
    }.
Arguments BuildAbstractDomain {_ _} _ _ _.
Arguments ad_car {_} _ /.
Arguments ad_gamma {_} _.
Arguments ad_sqsubseteq {_} _.
Arguments ad_mixin {_} _ /.
Global Hint Unfold ad_gamma : unfold_gamma.
Global Notation "(⊑[ A ])" := (@ad_sqsubseteq _ A).
Global Notation "a1 ⊑[ A ] a2" := (@ad_sqsubseteq _ A a1 a2) (at level 70).
Existing Instance ad_mixin.

Coercion abstract_domain_to_abstraction {C} (AD:abstract_domain C) : abstraction C :=
  @BuildAbstraction C (ad_car AD) (ad_gamma AD).
Canonical abstract_domain_to_abstraction.
Global Arguments abstract_domain_to_abstraction {_} _ /.
Global Hint Unfold abstract_domain_to_abstraction: unfold_gamma.

(** This is like OrderEmbedding/OrderPreserving, but is now a property
of an abstract domain, between the concrete order and abstract order. *)
Class ExactOrder {C} (A: abstract_domain C) :=
  exact_order: forall a1 a2, a1 ⊑[A] a2 <-> a1 ⊑γ[A] a2.

Class SoundOrder {C} (A: abstract_domain C) :=
  sound_order: forall a1 a2, a1 ⊑[A] a2 -> a1 ⊑γ[A] a2.
Global Instance ad_has_sound_order {C} (A: abstract_domain C): SoundOrder A.
Proof.
  apply: ad_γ_order_preserving.
Qed.

Global Instance ad_sqsubseteq_is_preorder {C} (A:abstract_domain C): PreOrder (⊑[A]).
Proof.
  apply: ad_sqsubseteq_preorder. 
Qed.

Global Instance ad_sqsubseteq_order_preserving {C} (A:abstract_domain C):
  OrderPreserving (ad_gamma A)  (⊑[A]) (⊆) .
Proof.
  apply: ad_γ_order_preserving. 
Qed.

(* Note: we need to help the typeclass resolution here, by directly
   providing the typeclasses deriving from firstorder. *)
Global Instance ad_sqsubseteq_is_reflexive {C} (A:abstract_domain C): Reflexive (⊑[A]).
Proof.
  assert(H:PreOrder (⊑[A])) by apply _.
  apply PreOrder_Reflexive.
Qed.

Global Instance ad_sqsubseteq_is_transitive {C} (A:abstract_domain C): Transitive (⊑[A]).
Proof.
  assert(H:PreOrder (⊑[A])) by apply _.
  apply PreOrder_Transitive.
Qed.

Definition ad_equiv_sqsubseteq {C} (A:abstract_domain C) : relation A :=
  fun a1 a2 => a1 ⊑[A] a2 /\ a2 ⊑[A] a1.

Global Notation "(⊑⊒[ A ])" := (@ad_equiv_sqsubseteq _ A).
Global Notation "a1 ⊑⊒[ A ] a2" := (@ad_equiv_sqsubseteq _ A a1 a2) (at level 70).

(** (⊑⊒[ A ]) is an equivalence relation. *)
Instance ad_equiv_equivalence {C} (A: abstract_domain C) : Equivalence (⊑⊒[ A ]).
Proof.
  assert(P:PreOrder (⊑[A])) by apply _.
  constructor.
  - move=> a. split; apply PreOrder_Reflexive.
  - move=> a1 a2 [H12 H21]. split; assumption.
  - move=> a1 a2 a3 [H121 H122] [H232 H233]. 
    assert(T:Transitive (⊑[A])) by apply _.
    split; transitivity a2; assumption.
Qed.

(** γ[A] is a morphism from (⊑⊒[ A ]) to (⊆⊇). *)
Instance ad_equiv_proper {C} (A:abstract_domain C): Proper ((⊑⊒[ A ]) ==> (⊆⊇)) (γ[A] ).
Proof.
  move => a1 a2 [H12 H21]. split; apply ad_γ_order_preserving; assumption.
Qed.

(** With ExactOrder, equal concretization implies abstract equivalence. *)
Lemma exact_order_gamma_equiv {C} (A: abstract_domain C) `{!ExactOrder A} a1 a2 :
  γ[A] a1 ⊆⊇ γ[A] a2 -> a1 ⊑⊒[A] a2.
Proof.
  move=> [H12 H21]. split; apply exact_order; assumption.
Qed.

(** An important property of an abstraction: that there is only one way
    to abstract a given set. This allows e.g. to test equality using
    hash-consing. When we have a Galois connection, injective gamma means
    that we have a Galois insertion. *)
Class IsGammaInjective {C} (A: abstract_domain C) : Prop :=
  is_gamma_injective :> Inj (⊑⊒[A]) (⊆⊇) (γ[A] ).

(** ExactOrder implies IsGammaInjective, but is a stronger property:
    we can be injective (different elements have different
    concretizations) without requiring that when one concretization is
    smaller than the other, this reflects in the abstract order. *)
Global Instance exact_order_gamma_injective {C} (A: abstract_domain C)
  `{!ExactOrder A} : IsGammaInjective A.
Proof.
  move=> a1 a2. apply (exact_order_gamma_equiv A).
Qed.

(** The converse is false: [IsGammaInjective] does not imply
    [ExactOrder]. Injectivity only constrains the abstract order on
    pairs whose concretizations are *equal*; nothing forces it to
    track strict γ-inclusion. The two-element domain below makes this
    concrete: distinct elements have distinct concretizations (so
    [IsGammaInjective] holds vacuously), one concretization is a
    strict subset of the other, yet the abstract order is just
    equality, so [ExactOrder] fails.

    Note that IsGammaInjective + the existence of a best abstraction
    does implies ExactOrder, which means that, here, there is no best
    abstraction. Indeed, neither true nor false are the best
    abstraction of the empty set, due to the abstract order. *)
Module IsGammaInjective_does_not_imply_ExactOrder.

  (* Carrier: bool. γ true = {tt}, γ false = ∅. Abstract order: eq. *)
  Definition gamma (b : bool) : propset unit :=
    if b then full_set else ∅.

  Definition sqsubseteq (b1 b2 : bool) : Prop := b1 = b2.

  Definition laws : abstract_domain_laws (A:=BuildAbstraction gamma) gamma sqsubseteq.
  Proof.
    refine {| ad_sqsubseteq_preorder := _ |}.
    - move=> b1 b2 ->. by [].    (* Order Preserving. *)
      Unshelve.
      split.
      + done.
      + by move=> b1 b2 b3 -> ->.
  Qed.

  Definition A : abstract_domain unit :=
    BuildAbstractDomain gamma sqsubseteq laws.

  Instance A_IsGammaInjective : IsGammaInjective A.
  Proof.
    move=> [|] [|] //= [H1 H2].
    - exfalso. by apply: H1.
    - exfalso. by apply: H2.
      Unshelve. all: done.
  Qed.

  Lemma A_not_ExactOrder : ~ ExactOrder A.
  Proof.
    move=> H. have /= := proj2 (H false true). clear H.
    have ->: (sqsubseteq false true) <-> False.
    { rewrite /sqsubseteq. easy. }
    move=> H; apply H; clear H.
    unfold_set; simpl. move=> c H.
    exfalso; easy.
  Qed.

  Local Definition IsAlpha `{A:abstract_domain C} (αS : A) (S : propset C)  : Prop :=
    forall a:A, S ⊆ γ[A] a <-> αS ⊑[A] a.

  Local Example not_best_abstraction: forall a:A, not (IsAlpha (a:A) ∅).
  Proof.
    move=> a. move /(_ (negb a))=> [H _].
    have Hyp: (∅ ⊆ (γ[A] ) (negb a)). by easy.
    move: H. move/(_ Hyp) => H. clear Hyp.
    case:a H => H; discriminate.
  Qed.
End IsGammaInjective_does_not_imply_ExactOrder.

(** * Galois connection and α relation. *)

(** This property is similar to the Galois connection property, but
    applied to a single pair of objects. *)
  Class IsAlpha `{A:abstract_domain C} (αS : A) (S : propset C)  : Prop :=
    is_alpha: forall a:A, S ⊆ γ[A] a <-> αS ⊑[A] a.
  Global Hint Unfold is_alpha IsAlpha: to_set.
  (** Todo: a notation fo isAlpha, maybe isα[A] as an infix, or ⊑⊒α[A] *)

  (** Because the α function is not constructible in Rocq, we define
      an α relation, that says whether S = α(a). The strong version is
      like an α function: it defines the necessary and sufficient
      condition to be the best abstraction of S. It is unique modulo
      equivalence. 

      Note that we do not require the definition of such a function in
      our abstract domain, as we can prove soundness and exactness
      without it (it is mostly useful to reason about best
      abstraction). *)
  Class StrongAlphaRelation `(A:abstract_domain C) :=
    { strong_α_relation: A -> propset C -> Prop;
      strong_α_relation_spec: forall a S, strong_α_relation a S <-> IsAlpha a S
    }.

  (** Usual abstract interpretation proofs, when we have a Galois
      connection, is done by rewriting sets under α functions. Because
      we don't have propositional extensionality in Rocq by default,
      this requires that the is_α relation is a morphism. This is
      always the case for strong alpha relations, but not for weak. *)
  Global Instance strong_α_proper {C} {A:abstract_domain C} `(WAR: !StrongAlphaRelation A) (a: A) :
    Proper ((⊆⊇) ==> iff) (strong_α_relation a).
  Proof.
    move=> SA SB H. rewrite! strong_α_relation_spec. to_set; unfold_set.
    rewrite /(_ ⊆⊇ _) !/(_ ⊆ _) in H. firstorder.
  Qed.

  (** A weak alpha relation is one that helps proving when an
     abstraction is the best abstraction of a set. It may fail to
     establish that an abstraction is the best in every case, but it
     does not matter if this suffices to prove that our transfer
     functions return the best element. The only problem is that it
     cannot be used to prove that a set has no best abstraction. *)
  Class WeakAlphaRelation `(A:abstract_domain C) :=
    { weak_α_relation: A -> propset C -> Prop;
      weak_α_relation_spec: forall a S, weak_α_relation a S -> IsAlpha a S;
      weak_α_relation_proper : forall a, Proper ((⊆⊇) ==> iff) (weak_α_relation a);
    }.

  Global Existing Instance weak_α_relation_proper.
  (* This makes the abstract domain argument visible. *)
  Arguments strong_α_relation {C} A {StrongAlphaRelation} a S.
  Arguments weak_α_relation {C} A {WeakAlphaRelation} a S.


  (* MAYBE: provide a common notation for the weak and strong α-relations, perhaps
     by making both instances of a single α-relation class. *)
  Notation "(≡α)" := weak_α_relation (at level 70).
  Infix "≡α" := weak_α_relation (at level 70).
  (* Global Hint Mode StrongAlphaRelation - ! : typeclass_instances. *)
  Notation "(≡α[ A ])" := (weak_α_relation A) (at level 10).
  Notation "a ≡α[ A ] S" := (weak_α_relation A a S) (at level 70, no associativity).
  

  Instance strong_alpha_relation_is_weak  `{SAR:StrongAlphaRelation C A} : WeakAlphaRelation A.
  Proof.
    refine {| weak_α_relation := strong_α_relation A (StrongAlphaRelation:=SAR) |}.
    abstract (by apply strong_α_relation_spec).
  Defined.
  

  
(** * Relations between an abstract and a concrete element. *)

(** A overapproximates S when γ a ⊇ S. *)
Class Overapproximates `{A:abstraction C}  (a : A) (S : propset C) : Prop :=
  overapproximates : S ⊆ γ[A] a.

(** a underapproximates S when γ a ⊆ S. *)
Class Underapproximates `{A:abstraction C}  (a : A) (S : propset C) : Prop :=
  underapproximates : γ[A] a ⊆ S.

(** a exactly represents S when γ a = S. *)
Class ExactlyRepresents `{A:abstraction C}  (a : A) (S : propset C) : Prop :=
  exactly_represents : γ[A] a ⊆⊇ S.

(* Note: we prefer the above equation over this form:
  Class ExactlyRepresents {A C} `{Concretization A C}  (a : A) (S : propset C) : Prop :=
    { exact_overapproximates :: Overapproximates a S;
      exact_underapproximates :: Underapproximates a S;
      exact_def : γ a ≡ S
    }.

  Because it allows unfolding, and thus simplifies rewriting. Hence, we declare the derived
  instances manually. *)

Hint Unfold overapproximates underapproximates exactly_represents
  Overapproximates Underapproximates ExactlyRepresents: to_set. 


(** This says that γ αS is a lower bound of for the abstractions that overapproximate S. *)
Class UpperBoundInPrecision `{A:abstraction C} (αS : A) (S : propset C)  : Prop :=
  upper_bound_in_precision : forall a:A, Overapproximates a S -> Overapproximates a ( γ[A] αS).

Lemma upper_bound_in_precision_iff `{A:abstraction C} (αS: A) (S : propset C):
  UpperBoundInPrecision αS S <-> forall a, S ⊆ γ[A] a -> γ[A] αS ⊆ γ[A] a.
Proof. done. Qed.
Hint Rewrite @upper_bound_in_precision_iff: to_set.

(* We don't want to set_unfold this, because it is unreadable. *)
(* Global Instance set_unfold_upper_bound_in_precision {A C} `{Gamma:A:abstraction C} (αS : A) (S : propset C) : *)
(*   SetUnfold (UpperBoundInPrecision αS S) *)
(*     (forall x : A, (forall c : C, c ∈ S → c ∈ γ x) → (forall c : C, c ∈ γ αS → c ∈ γ x)). *)
(* Proof. constructor. autorewrite with to_set. now set_unfold. Qed. *)

(** αS is a most precise abstraction of S if αS is one of the elements
    that approximates S that has the smallest concretization.

    Note that there may be several most-precise abstraction
    (especially, some that may be more precise than others when
    considering the abstract order). *)
Class MostPrecise `{A:abstraction C} (αS : A) (S : propset C)  : Prop := {
    most_precise_overapproximates :: Overapproximates αS S ;
    most_precise_is_optimal :: UpperBoundInPrecision αS S
  }.

Lemma most_precise_iff `{A:abstraction C} (αS : A) (S : propset C) :
  MostPrecise αS S <-> (Overapproximates αS S /\ UpperBoundInPrecision αS S).
Proof.
  split. 
  - intros H; split; apply H.
  - intros [H1 H2]. constructor; assumption.
Qed.
Hint Rewrite @most_precise_iff: to_set.    


Class BestAbstraction `{A:abstract_domain C} (αS : A) (S : propset C)  : Prop := {
    best_abstraction_overapproximates :: Overapproximates αS S ;
    best_abstraction_is_optimal : forall a:A, Overapproximates a S -> αS ⊑[A] a
  }.
Lemma best_abstraction_iff `{A:abstract_domain C} (αS : A) (S : propset C) :
  BestAbstraction αS S <-> (Overapproximates αS S /\ forall a:A, Overapproximates a S -> αS ⊑[A] a).
Proof.
  split. 
  - intros H; split; apply H.
  - intros [H1 H2]. constructor; assumption.
Qed.
Hint Rewrite @best_abstraction_iff: to_set.

(** [BestAbstraction] is invariant under extensional set equality. *)
Lemma best_abstraction_equiv `{A:abstract_domain C} (a:A) (S S': propset C) :
  BestAbstraction a S -> S ⊆⊇ S' -> BestAbstraction a S'.
Proof.
  move=> [Hover Hopt]; rewrite propset_equiv_iff => Heq; split.
  - move=> z Hz; apply Hover, Heq, Hz.
  - move=> b Hb; apply Hopt => z Hz; apply Hb, Heq, Hz.
Qed.

(** [IsAlpha] is invariant under extensional set equality. Provided in
    two forms — pointwise ([forall z, z ∈ S1 <-> z ∈ S2]) and propset-equiv
    ([⊆⊇]) — since both shapes arise naturally at call sites. *)
Lemma IsAlpha_set_equiv `{A: abstract_domain C} (a: A) (S1 S2: propset C) :
  (forall z, z ∈ S1 <-> z ∈ S2) ->
  IsAlpha a S1 -> IsAlpha a S2.
Proof.
  move=> Heq H1 b; rewrite -(H1 b).
  by split; move=> Hsub z Hz; apply Hsub; apply Heq.
Qed.

Lemma is_alpha_set_equiv `{A : abstract_domain C} (a : A) (S S' : ℘ C) :
  S ⊆⊇ S' -> IsAlpha a S -> IsAlpha a S'.
Proof. move=> /propset_equiv_iff; exact: IsAlpha_set_equiv. Qed.

(** ** Relation between relations between an abstract and concrete elements. *)

(** Exactness (γ-completeness) and IsAlpha (α-completeness) are
    independent notions, except when the concrete and abstract order
    coincide (γ is order-embedding); in this case, exactness is
    stronger. Both implies maximal precision, which implies
    Overapproximates. Exactness also implies Underapproximates.

   We can thus make a nice diagram out of these notions:
<<
  ExactlyRepresents -> Underapproximates

  ExactlyRepresents -> MostPrecise -> Overapproximates
  BestAbstraction -> MostPrecise -> Oveapproximates.

  IsAlpha <-> BestAbstraction

  When ExactOrder: Exactlyrepresents -> MostPrecise <-> BestAbstraction.
>>
*)

Instance Exactly_represents_overapproximates
  `{A:abstraction C}  (a : A) (S : propset C) `{!ExactlyRepresents a S}: Overapproximates a S.
Proof. firstorder. Qed.

Instance Exactly_represents_underapproximates
  `{A:abstraction C}  (a : A) (S : propset C) `{!ExactlyRepresents a S}: Underapproximates a S.
Proof. firstorder. Qed.


Lemma exact_is_most_precise
  `{A:abstract_domain C} (αS : A) (S : propset C) :
  ExactlyRepresents αS S -> MostPrecise αS S.
Proof.
  move=> [Hunder Hover]. split.
  - exact Hover.                (* Soundness. *)
  - move=> a Hsounda. to_set in *. by transitivity S. (* Optimality. *)
Qed.
      
Lemma is_alpha_is_most_precise `{A:abstract_domain C} (αS : A) (S : propset C) :
  IsAlpha αS S -> MostPrecise αS S.
Proof.
  to_set.
  move=> Hadj. split.
  - (* Soundness: S ⊆ γ αS *)
    rewrite Hadj.
    (* assert(Reflexive (⊑[A])) by apply _. *)
    reflexivity.
  - (* Optimality. *)
    move=> a Hinc. apply: ad_γ_order_preserving.
    apply (Hadj a). exact Hinc.
Qed.

Lemma is_alpha_overapproximates `{A:abstract_domain C} (αS : A) (S : propset C) :
  IsAlpha αS S -> Overapproximates αS S.
Proof.
  move=> Hadj.
  apply: most_precise_overapproximates.
  apply: is_alpha_is_most_precise.
Qed.

Lemma is_alpha_is_best_abstraction `{A:abstract_domain C} (αS : A) (S : propset C) :
  IsAlpha αS S -> BestAbstraction αS S.
Proof.
  move=> Hadj. split.
  - apply: is_alpha_overapproximates.
  - unfold IsAlpha in *. firstorder.
Qed.

Lemma best_abstraction_is_is_alpha `{A:abstract_domain C} (αS : A) (S : propset C) :
  BestAbstraction αS S -> IsAlpha αS S.
Proof.
  move=> [Hover Hbest]. split.
  - apply: Hbest.
  - move=> H. transitivity ( γ[A] αS).
    + apply: Hover.
    + apply: ad_γ_order_preserving. exact H.
Qed.

Lemma is_alpha_iff_best_abstraction `{A:abstract_domain C} (αS : A) (S : propset C) :
  IsAlpha αS S <-> BestAbstraction αS S.
Proof.
  split.
  - apply is_alpha_is_best_abstraction.
  - apply best_abstraction_is_is_alpha.
Qed.

(** If we add an additional hypothesis, which is that γ is
    order-embedding (which is the same as order-reflecting, as it is
    already order-preserving), then MostPrecise is the same as
    being an IsAlpha. Otherwise, it is a weaker notion.

    Indeed a most-precise in the concrete element can be non-reduced.  For
    instance on intervals, [8,3] is a most precise representation
    of the empty set (in the concrete), but not in the abstract, as
    [9,2] is more precise. *)
Lemma most_precise_is_is_alpha `{A:abstract_domain C}
  `{H:!ExactOrder A} 
  (* `{H:@OrderEmbedding C A (ad_gamma A) (ad_sqsubseteq A)} *) (αS : A) (S : propset C) :
  MostPrecise αS S <-> IsAlpha αS S.
Proof.
  split. 2: apply is_alpha_is_most_precise.
  move=> [Hsound Hbest].  split.
  - (* If S ⊆ γ a then αS ⊑γ a (This is exactly optimality) *)
    to_set in *.
    rewrite H. apply: Hbest. 
  - (* Right to Left: If αS ⊑γ a' then S ⊆ γ a' *)
    move=> Hle. transitivity ( γ[A] αS).
    + exact: Hsound.
    + apply: (proj1 (H αS a)). exact: Hle.
Qed.


(* Note: the proofs are simpler if we start from best_abstraction than is_alpha. *)
Lemma best_abstraction_is_most_precise `{A:abstract_domain C} (αS : A) (S : propset C) :
  BestAbstraction αS S -> MostPrecise αS S.
Proof.
  to_set.
  move=> [Hsound Hopt]. split.
  - (* Soundness*) exact Hsound.
  - (* Optimality*) move=> a Hinc.
    apply: ad_γ_order_preserving.
    apply: Hopt.
    exact Hinc.
Qed.

Lemma most_precise_is_best_abstraction `{A:abstract_domain C}
  `{H:!ExactOrder A} 
  (* `{H:@OrderEmbedding C A (ad_gamma A) (ad_sqsubseteq A)} *) (αS : A) (S : propset C) :
  MostPrecise αS S -> BestAbstraction αS S.
Proof.
  move=> [Hsound Hbest].  split.
  - apply Hsound.
  - move=> a Hle. apply H. apply Hbest. apply Hle.
Qed.


(* In general, being exact (γ-complete) is not a guarantee of being
   the most precise in the abstract order. For instance, [8,3] exactly
   represents the empty set, but is not the most precise relation in
   the abstract: [9,2] is more precise.

   It works only if the abstract and concrete order exactly correspond. *)
Lemma exact_is_is_alpha `{A:abstract_domain C} (αS : A) (S : propset C)
  `{H:!ExactOrder A} :
  ExactlyRepresents αS S -> IsAlpha αS S.
Proof.
  move=> ER.
  apply most_precise_is_is_alpha.
  apply: exact_is_most_precise.
Qed.

(** * Reductions. *)

(** ** Maximally reduced abstract elements.

    An abstract element [a] is *maximally reduced* when it is the best
    abstraction of the element that it represents. Note that this is
    stronger than being minimal (in the abstract order [⊑]) among
    elements with concretization [γ a]. *)
Class MaximallyReduced `{A: abstract_domain C} (a : A) : Prop := maximally_reduced: BestAbstraction a (γ[A] a).

(** The α-image of any set is maximally reduced: if [a] is the best
    abstraction of [S], then [a] is also the best abstraction of [γ a].
    This is the reusable bridge from α-completeness to maximal
    reduction. Optimality: any [a'] over-approximating [γ a] has
    [S ⊆ γ a ⊆ γ a'], hence [a ⊑ a'] by [IsAlpha]. *)
Lemma is_alpha_maximally_reduced `{A: abstract_domain C} (a : A) (S : ℘ C) :
  IsAlpha a S -> MaximallyReduced a.
Proof.
  move=> Ha. split.
  - done.
  - move=> a' Ha'. apply (Ha a'). transitivity (γ[A] a).
    + exact: (is_alpha_overapproximates _ _ Ha).
    + exact: Ha'.
Qed.


(** An abstract element [a] is *weakly maximally reduced* when it is
   minimal (in the abstract order [⊑]) among elements with
   concretization [γ a]. Equivalently: any [a'] with the same
   concretization as [a]. *)
Class MaximallyReducedWeak `{A: abstract_domain C} (a : A) : Prop :=
  maximally_reduced_weak : forall a' : A, γ[A] a' ⊆⊇ γ[A] a -> a ⊑[A] a'.



(** [MaximallyReduced a] is a stronger property than
    [MaximallyReducedWeak a]: it requires [a] to be below every
    over-approximation of [γ a], not just below every element with the
    same concretization.

   Exemple: lattice with two elements a=false b=true, γ a = {}, γ b = {0},
   but we don't have a ⊑ b. Then:
   - a is maximally reduced (sole element with this concretisation)
   - a is not maximally reduced: γ a ⊆ γ b, but we don't have a ⊑ b. *)
Example maximally_reduced_differs_from_maximally_reduced_weak:
  exists C:Type, exists A: abstract_domain C, exists a:A, MaximallyReducedWeak a /\ ~(MaximallyReduced a).
Proof.
  exists unit. exists (IsGammaInjective_does_not_imply_ExactOrder.A). exists false. split.
  - (* false is maximally reduced weak: sole element with this concretization.  *)
    move=> b. case: b; simpl; move=> H.
    + exfalso; by timeout 1 firstorder.
    + reflexivity.
  - (* false is not maximally reduced, as we don't have false ⊑ true.  *)
    move=> [_ Hopt].
    move: (Hopt true) => H. clear Hopt. to_set in H.
    have H2: ~(false ⊑[ IsGammaInjective_does_not_imply_ExactOrder.A] true).
    { move=> H3. hnf in H3. discriminate. }
    apply H2. apply H. easy.
Qed.

Lemma maximally_reduced_implies_weak `{A: abstract_domain C} (a : A) :
  MaximallyReduced a -> MaximallyReducedWeak a.
Proof.
  move=> [_ Hbest] a' Heq.
  apply: Hbest.
  apply Heq.
Qed.

(** When [γ] is order-embedding (ExactOrder), the two notions coincide. *)
Lemma maximally_weak_iff_maximally_reduced_when_exact_order `{A: abstract_domain C} `{!ExactOrder A}
  (a : A) : MaximallyReducedWeak a <-> MaximallyReduced a.
Proof.
  split; last by apply: maximally_reduced_implies_weak.
  move=> Hopt.
  split; first done.
  move=> b Hover.
  apply exact_order. to_set in *. exact: Hover.
Qed.

(** ** Reduction functions.

    A *reduction* is an endo-function on an abstract domain that
    refines its input in the abstract order while preserving the
    concretization. Reductions are the engine of reduced products:
    they propagate cross-domain information without changing what the
    abstract value denotes. *)
Class Reduction `{A: abstract_domain C} (red : A -> A) : Prop := 
  { reduction_refines : forall a, red a ⊑[A] a;
    reduction_preserves_gamma : forall a, γ[A] (red a) ⊆⊇ γ[A] a; }.

(** Reductions preserve over-approximation: if [a] over-approximates
    [S], so does [red a]. *) 
Lemma reduction_overapproximates `{A: abstract_domain C} (red : A -> A)
  `{!Reduction red} (a : A) (S : propset C) :
  Overapproximates a S -> Overapproximates (red a) S.
Proof.
  move=> Hover. to_set in *. 
  transitivity ((γ[A] ) a); first done.
  apply reduction_preserves_gamma.
Qed.

(** An *maximal reduction* just returns the best abstraction.  *)
Class MaximalReduction `{A: abstract_domain C} (red : A -> A) : Prop :=
  { maximal_reduction_is_reduction :: Reduction red;
    maximal_reduction_maximally_reduced : forall a, MaximallyReduced (red a) }.

(** Maximal reductions are idempotent in the abstract-equivalence sense [⊑⊒]. *)
Lemma maximal_reduction_idempotent `{A: abstract_domain C} (red : A -> A)
  `{!MaximalReduction red} (a : A) : red (red a) ⊑⊒[A] red a.
Proof.
  split.
  - exact: reduction_refines.
  - have H:= MaximallyReduced (red a).
    { apply maximal_reduction_maximally_reduced.
      apply reduction_preserves_gamma.
    }
Qed.

(** The standard recipe for maximal reduction in abstract interpretation
    is α ∘ γ. We adapt this to when α is a relation. *)
Lemma best_abstraction_is_maximal_reduction `{A: abstract_domain C} (red : A -> A) :
  (forall a, BestAbstraction (red a) (γ[A] a)) -> MaximalReduction red. 
Proof.
  move=> Hba.
  have Hred : Reduction red.
  { split=> a; have [Hover Hbest] := Hba a.
    - by apply: Hbest.
    - split.
      + (* γ (red a) ⊆ γ a *)
        apply: ad_γ_order_preserving.
        by apply: Hbest.
      + (* γ a ⊆ γ (red a) *)
        exact: Hover. }
  refine {| maximal_reduction_is_reduction := Hred |}.
  move=> a.
  have Heq: ((γ[A] ) (red a)) ⊆⊇ ((γ[A] ) a). by apply reduction_preserves_gamma.
  (* We would just want to rewrite here, but we can't; we unfold + use
  transitivity instead. *)
  have [Hover Hbest] := Hba a. 
  unfold MaximallyReduced.
  split.
  - to_set. by transitivity ((γ[A] ) (red a)).
  - move=> a' Ha'.  apply: Hbest. to_set in *. by transitivity ((γ[A] ) (red a)).
Qed.

 
(** Core Galois connection properties. *)

(** Extensivity is normally S ⊆ \gamma o \alpha S. In our relational settings, it corresponds to is_alpha_overapproximates. *)
Lemma gamma_alpha_extensive `(A:abstract_domain C) αS S: IsAlpha αS S -> S ⊆ γ[A] αS.
Proof.
  exact: is_alpha_overapproximates.
Qed.

(** Gamma o alpha is an upper closure operator, and thus idempotent on elements representable by an abstract element. *)
Lemma gamma_alpha_idempotent `(A:abstract_domain C) a2 a1:
  IsAlpha a1 (γ[A] a2) -> γ[A] a1 ⊆⊇ γ[A] a2.
Proof.
  move=> H. split.
  - apply: ad_γ_order_preserving. by apply H.
  - exact: (is_alpha_overapproximates _ _ H).
Qed.

Lemma alpha_gamma_reductive `(A:abstract_domain C) a2 a1:
  IsAlpha a1 (γ[A] a2) -> a1 ⊑[A] a2.
Proof.  move=> H. apply H. reflexivity.
Qed.

(** The [α ∘ γ ∘ α = α] identity: if [a] is an alpha of [S] and [b] is
    an alpha of [γ a] (a re-abstraction of [a]), then [b] is again an
    alpha of [S]. This is what makes α-completeness survive a
    [Reduction], which computes the alpha of its input's γ. *)
Lemma alpha_gamma_alpha_is_alpha `(A:abstract_domain C) (a b : A) (S : propset C):
  IsAlpha a S -> IsAlpha b (γ[A] a) -> IsAlpha b S.
Proof.
  move=> Ha Hb a'. split.
  - move=> HS. apply Hb.
    apply: ad_γ_order_preserving. by apply Ha.
  - move=> Hle. transitivity (γ[A] a).
    + exact: (is_alpha_overapproximates _ _ Ha).
    + by apply Hb.
Qed.

Lemma alpha_monotone `(A:abstract_domain C) a1 S1 a2 S2:
  IsAlpha a2 S2 -> IsAlpha a1 S1 -> S1 ⊆ S2 -> a1 ⊑[A] a2.
Proof.
  move=> H2 H1 H12conc.
  rewrite /IsAlpha in H1.
  apply (H1 a2).
  transitivity S2.
  - exact H12conc.
  - by apply: gamma_alpha_extensive.
Qed.

(** * Galois insertions and their relation to reduction. *)

(** We have two different notions of Galois insertion,
    IsGammaInjective and ExactOrder. The difference between both is
    that we can be Gammainjective without having ExactOrder if we
    don't have a Galois connection: more precisely, if the
    concretization (γ a) of some abstract element a has no best
    abstraction.

    Moreover, ExactOrder <=> every element is MaximallyReduced;
    IsGammaInjective <=> every element is weakly MaximallyReduced. *)

(** Galois connection + Injectivity => ExactOrder. By transivity. *)
Global Instance gamma_injective_and_galois_connection_exact_order {C} (A: abstract_domain C)
  (HGalois:forall a:A, exists a':A, IsAlpha a' (γ[A] a))
  `{GInj:!IsGammaInjective A} : ExactOrder A.
Proof.
  move=> a1 a2.
  split; [apply: ad_γ_order_preserving|].  to_set. move =>H12conc.
  have [a1' H1]: exists a1':A, IsAlpha a1' (γ[A] a1) by apply HGalois.
  have [a2' H2]: exists a2':A, IsAlpha a2' (γ[A] a2) by apply HGalois.
  have H12: a1' ⊑[ A] a2' by apply: alpha_monotone.
  have H11: a1' ⊑⊒[ A] a1. { apply: GInj. apply: gamma_alpha_idempotent. }
  have H22: a2' ⊑⊒[ A] a2. { apply: GInj. apply: gamma_alpha_idempotent. }
  transitivity a1'.
  - apply H11.
  - transitivity a2'.
    + apply H12.
    + apply H22.
Qed.


(** Maximally_Reduced_Weak is a kind of local injectivity: because the
    premise is symmmetric (γ[A] a' ⊆⊇ γ[A] a), the conclusion must be
    too (a'⊑⊒[A] a), when applied to all elements.  *)
Lemma injectivity_is_all_maximally_reduced_weak {C} (A: abstract_domain C):
  (forall a:A, MaximallyReducedWeak a) <-> IsGammaInjective A.
Proof.
  split.
  - (* => Is Gamma Injective. *)
    move=>H a b Heqγab. split.
    + apply H. by symmetry.
    + by apply H.
  - (* => All Maximallyreducedweak. *)
    move=> H a b Hab. by apply H.
Qed.

(** MaximallyReduced is also a local occurence of ExactOrder. *)
Lemma exact_order_is_all_maximally_reduced {C} (A: abstract_domain C):
  (forall a:A, MaximallyReduced a) <-> ExactOrder A.
Proof.
  split.
  - (* => ExactOrder. *)
    move=> H a b. split; first by apply sound_order. 
    move=>Heqγab. apply H. exact Heqγab.
  - (* => All MaximallyReduced. *)
    move=> H a. split.
    + done.                     
    + move=> b Hab. apply H. exact Hab.
Qed.

(** ExactOrder is Injectivity plus a weak form of galois connection:
    we only need at least one best element for every possible
    concretization (usual galois connection is exactly one best
    element for every set, which is much more restrictive).  *)
Lemma exact_order_is_injectivity_plus_galois_connection {C} (A: abstract_domain C):
  ExactOrder A <-> (IsGammaInjective A /\ (forall a:A, exists a':A, IsAlpha a' (γ[A] a))).
Proof.
  split.
  - (* ExactOrder => IsGammaInjective + Galois connection. *)
    move=> HExactOrder. split.
    + by apply: exact_order_gamma_injective.
    + move=> a. exists a. rewrite is_alpha_iff_best_abstraction.
      by apply exact_order_is_all_maximally_reduced.
  - (* Injective + Galois connection => ExactOrder. *)
    move=> [Hinj HGalois] a b.
    by apply gamma_injective_and_galois_connection_exact_order.
Qed.    

(** * Set operations and transformations. *)

Definition setop1 (C1 C0 : Type) := propset C1 → propset C0.  
Definition setop2 (C2 C1 C0 : Type) := propset C2 → propset C1 → propset C0.
Definition setop3 (C3 C2 C1 C0 : Type) := propset C3 -> propset C2 → propset C1 → propset C0.  

(* We use this scheme:

     collecting[_partial|_total][_unary|_binary][_forward|_backward][_left|_right]

     but with _unary and _total being omitted (as they are the
     default).

 *)

Definition collecting_forward
  {C1 C0: Type} (f: C1 -> C0) : setop1 C1 C0 :=
  λ S1, {[c0 | ∃ c1, c1 ∈ S1 ∧ f c1 = c0]}.

Definition collecting_backward
  {C1 C0: Type} (f: C1 -> C0) : setop2 C1 C0 C1 :=
  λ S1 S0, {[c1 | ∃ c0, c1 ∈ S1 ∧ c0 ∈ S0 ∧ f c1 = c0]}.

Definition collecting_binary_forward
  {C2 C1 C0: Type} (f: C2 -> C1 -> C0) : setop2 C2 C1 C0 :=
  λ S2 S1, {[c0 | ∃ c2 c1, c2 ∈ S2 ∧ c1 ∈ S1 ∧ f c2 c1 = c0]}.

(** Partial variant: only pairs [(c2, c1)] satisfying the predicate [P]
    contribute to the result set. Used to model genuinely partial
    operations (e.g. division with divisor ≠ 0): when [P] excludes every
    pair in [S2 × S1], the resulting concrete set is empty. *)
Definition collecting_binary_forward_partial
  {C2 C1 C0: Type} (P: C2 -> C1 -> Prop) (f: C2 -> C1 -> C0) : setop2 C2 C1 C0 :=
  λ S2 S1, {[c0 | ∃ c2 c1, c2 ∈ S2 ∧ c1 ∈ S1 ∧ P c2 c1 ∧ f c2 c1 = c0]}.

(* We use _left and _right (for the position of arguments) as it is less confusing than 2 and 1. *)
Definition collecting_binary_backward_left
  {C2 C1 C0: Type} (f: C2 -> C1 -> C0) : setop3 C2 C1 C0 C2 :=
  λ S2 S1 S0, {[c2 | ∃ c1 c0, c2 ∈ S2 ∧ c1 ∈ S1 ∧ c0 ∈ S0 ∧ f c2 c1 = c0]}.

Definition collecting_binary_backward_right
  {C2 C1 C0: Type} (f: C2 -> C1 -> C0) : setop3 C2 C1 C0 C1 :=
  λ S2 S1 S0, {[c1 | ∃ c2 c0, c2 ∈ S2 ∧ c1 ∈ S1 ∧ c0 ∈ S0 ∧ f c2 c1 = c0]}.

Global Hint Unfold
  collecting_forward
  collecting_backward
  collecting_binary_forward
  collecting_binary_forward_partial
  collecting_binary_backward_left
  collecting_binary_backward_right : to_set.

(** [collecting_binary_forward] distributes over [∪] in either argument,
    plus respects [⊆⊇] in the other. Used to discharge the [fC]
    distributivity hypothesis of [binary_alpha_complete_split_{l,r}] at
    split call sites. The combined statement [fC S T1 ⊆⊇ fC S_a T1 ∪ fC S_b T1]
    given [S ⊆⊇ S_a ∪ S_b] follows in one step. *)
Lemma collecting_binary_forward_union_l
  {C2 C1 C0: Type} (f: C2 -> C1 -> C0) (S2_a S2_b : propset C2) (T1 : propset C1) :
  collecting_binary_forward f (S2_a ∪ S2_b) T1 ⊆⊇
  collecting_binary_forward f S2_a T1 ∪ collecting_binary_forward f S2_b T1.
Proof.
  unfold_set_equiv => z; unfold_set; split.
  - move=> [c2 [c1 [Hor [Hc1 Heq]]]].
    case: Hor => Hc2; [left | right]; by exists c2, c1.
  - move=> [[c2 [c1 [Hc2 [Hc1 Heq]]]] | [c2 [c1 [Hc2 [Hc1 Heq]]]]];
      exists c2, c1; (repeat split=> //); by [left | right].
Qed.

Lemma collecting_binary_forward_union_r
  {C2 C1 C0: Type} (f: C2 -> C1 -> C0) (T2 : propset C2) (S1_a S1_b : propset C1) :
  collecting_binary_forward f T2 (S1_a ∪ S1_b) ⊆⊇
  collecting_binary_forward f T2 S1_a ∪ collecting_binary_forward f T2 S1_b.
Proof.
  unfold_set_equiv => z; unfold_set; split.
  - move=> [c2 [c1 [Hc2 [Hor Heq]]]].
    case: Hor => Hc1; [left | right]; by exists c2, c1.
  - move=> [[c2 [c1 [Hc2 [Hc1 Heq]]]] | [c2 [c1 [Hc2 [Hc1 Heq]]]]];
      exists c2, c1; (repeat split=> //); by [left | right].
Qed.

(** * Soundness theorems. *)
Section Unary.

  Context `(A1: abstraction C1). (* Concretization of the argument. *)
  Context `(A0: abstraction C0). (* Concretization of the result. *)  

  Local Notation γ1 := (γ[A1] ).
  Local Notation γ0 := (γ[A0] ).
  
  Variable fA : A1 -> A0.
  Variable fC: setop1 C1 C0.

  Definition unary_spec rel := forall a1, rel (fA a1) (fC (γ1 a1)).  
  (** In terms of precision, we have exact => best => overapproximation, and exact => underapproximation. *)
  Definition unary_overapproximation  := unary_spec Overapproximates.
  Definition unary_most_precise  := unary_spec MostPrecise.
  Definition unary_underapproximation  := unary_spec Underapproximates.
  Definition unary_exact := unary_spec ExactlyRepresents.

End Unary.

(* best means something only if we have an abstract order. *)
Definition unary_best
  {C1 : Type} (A1 : abstract_domain C1)
  {C0 : Type} (A0 : abstract_domain C0) (fA : A1 -> A0) (fC: setop1 C1 C0)
  := forall a1, BestAbstraction (fA a1) (fC ( γ[A1] a1)).


Section Binary.

  Context `(A2: abstraction C2). (* Concretization of the left argument. *)  
  Context `(A1: abstraction C1). (* Concretization of the right argument. *)
  Context `(A0: abstraction C0). (* Concretization of the result. *)  

  Local Notation γ2 := ( γ[A2] ).  
  Local Notation γ1 := ( γ[A1] ).
  Local Notation γ0 := ( γ[A0] ).

  Variable fA : A2 -> A1 -> A0.
  Variable fC: setop2 C2 C1 C0.

  (** In terms of precision, we have exact => best => overapproximation, and exact => underapproximation. *)
  Definition binary_overapproximation  := forall a2 a1, Overapproximates (fA a2 a1) (fC (γ2 a2) (γ1 a1)).
  Definition binary_most_precise  := forall a2 a1, MostPrecise (fA a2 a1) (fC (γ2 a2) (γ1 a1)).
  Definition binary_underapproximation  := forall a2 a1, Underapproximates (fA a2 a1) (fC (γ2 a2) (γ1 a1)).
  Definition binary_exact  := forall a2 a1, ExactlyRepresents (fA a2 a1) (fC (γ2 a2) (γ1 a1)).    

End Binary.

(* best means something only if we have an abstract order. *)
Definition binary_best
  {C2 : Type} (A2 : abstract_domain C2) {C1 : Type} (A1 : abstract_domain C1)
  {C0 : Type} (A0 : abstract_domain C0) (fA : A2 -> A1 -> A0) (fC: setop2 C2 C1 C0)
  := forall a2 a1, BestAbstraction (A:=A0) (fA a2 a1) (fC ( γ[A2] a2) ( γ[A1] a1)).

(** α-completeness of a binary transfer function, at a given pair of
    abstract elements and concrete sets: if [a2], [a1] are the best
    abstractions of [S2], [S1], then [fA a2 a1] is the best abstraction
    of [fC S2 S1]. *)
Definition binary_alpha_complete
  {C2 : Type} (A2 : abstract_domain C2) {C1 : Type} (A1 : abstract_domain C1)
  {C0 : Type} (A0 : abstract_domain C0) (fA : A2 -> A1 -> A0) (fC: setop2 C2 C1 C0)
  (a2 : A2) (a1 : A1) (S2 : propset C2) (S1 : propset C1)
  := IsAlpha (A:=A2) a2 S2 -> IsAlpha (A:=A1) a1 S1 ->
     IsAlpha (A:=A0) (fA a2 a1) (fC S2 S1).

(** Pointwise bridge from [binary_alpha_complete] (stated with [IsAlpha])
    to [BestAbstraction]. The operand witnesses are supplied as
    [MaximallyReduced] instances — i.e. each operand is the best
    abstraction of its own concretization. No [ExactOrder] is needed, so
    this remains usable on domains (like raw [itv]) where [ExactOrder]
    fails but the operands at hand happen to be maximally reduced. *)
Lemma binary_alpha_complete_to_best
  `(A2: abstract_domain C2) `(A1: abstract_domain C1) `(A0: abstract_domain C0)
  (fA : A2 -> A1 -> A0) (fC : setop2 C2 C1 C0)
  (a2 : A2) (a1 : A1)
  `{!MaximallyReduced (A:=A2) a2} `{!MaximallyReduced (A:=A1) a1} :
  binary_alpha_complete A2 A1 A0 fA fC a2 a1 (γ[A2] a2) (γ[A1] a1) ->
  BestAbstraction (A:=A0) (fA a2 a1) (fC (γ[A2] a2) (γ[A1] a1)).
Proof.
  move=> Hac.
  have Hα2 : IsAlpha a2 (γ[A2] a2) by apply: best_abstraction_is_is_alpha.
  have Hα1 : IsAlpha a1 (γ[A1] a1) by apply: best_abstraction_is_is_alpha.
  exact: is_alpha_is_best_abstraction (Hac Hα2 Hα1).
Qed.

(** [ExactOrder] corollary: when both operand domains have [ExactOrder],
    every element is maximally reduced, so pointwise [binary_alpha_complete]
    at all [γ]-pairs lifts to the universal [binary_best]. *)
Lemma binary_alpha_complete_to_binary_best
  `(A2: abstract_domain C2) `(A1: abstract_domain C1) `(A0: abstract_domain C0)
  `{!ExactOrder A2} `{!ExactOrder A1}
  (fA : A2 -> A1 -> A0) (fC : setop2 C2 C1 C0) :
  (forall a2 a1, binary_alpha_complete A2 A1 A0 fA fC a2 a1 (γ[A2] a2) (γ[A1] a1)) ->
  binary_best A2 A1 A0 fA fC.
Proof.
  move=> Hac a2 a1.
  have MR2 : MaximallyReduced (A:=A2) a2
    by apply exact_order_is_all_maximally_reduced.
  have MR1 : MaximallyReduced (A:=A1) a1
    by apply exact_order_is_all_maximally_reduced.
  exact: (binary_alpha_complete_to_best A2 A1 A0 fA fC a2 a1 (Hac a2 a1)).
Qed.

Section Ternary.

  Context `(A3: abstraction C3).
  Context `(A2: abstraction C2). 
  Context `(A1: abstraction C1).
  Context `(A0: abstraction C0).

  Local Notation γ3 := ( γ[A3] ).    
  Local Notation γ2 := ( γ[A2] ).  
  Local Notation γ1 := ( γ[A1] ).
  Local Notation γ0 := ( γ[A0] ).

  Variable fA : A3 -> A2 -> A1 -> A0.
  Variable fC: setop3 C3 C2 C1 C0.

  Definition ternary_spec rel := forall a3 a2 a1, rel (fA a3 a2 a1) (fC (γ3 a3) (γ2 a2) (γ1 a1)).
  Definition ternary_overapproximation  := ternary_spec Overapproximates.
  Definition ternary_best  := ternary_spec MostPrecise.
  Definition ternary_underapproximation  := ternary_spec Underapproximates.
  Definition ternary_exact := ternary_spec ExactlyRepresents.
  

End Ternary.

Global Hint Unfold
  unary_spec unary_overapproximation unary_most_precise unary_best unary_underapproximation unary_exact
  (* binary_spec *) binary_overapproximation binary_most_precise binary_best binary_underapproximation binary_exact binary_alpha_complete
  ternary_spec ternary_overapproximation ternary_best ternary_underapproximation ternary_exact
  : to_set.

(** * Low-level interface of transfer functions *)

(** Our current interface for single-value abstraction: return None if
    no improvement, or Some a1' if we improved it.
    TODO: this interface cannot say that the refinement is empty; it should be
    able to report bottom as well. *)
Definition backward_unary_function_correct
  `{A1:abstract_domain C1} `{A0:abstraction C0} `{Equiv A1} f' (f: A1 -> A0 -> A1) :=
  forall a1 a0, match f' a1 a0 with
           | None => f a1 a0 ≡ a1
           | Some a1' => f a1 a0 = a1' ∧ a1' ⊑[A1] a1 /\ a1' ≢ a1
           end.

Definition backward_binary_function_correct
  `{A2: abstract_domain C2} `{A1: abstract_domain C1} `{A0: abstraction C0} `{Equiv A2} `{Equiv A1}
  f' (fleft: A2 -> A1 -> A0 -> A2) (fright: A2 -> A1 -> A0 -> A1) :=
  forall a2 a1 a0,
    match f' a2 a1 a0 with
    | (r2, r1) =>
          (match r2 with 
           | None => fleft a2 a1 a0 ≡ a2
           | Some a2' => fleft a2 a1 a0 = a2' ∧ a2' ⊑[A2]  a2 /\ a2' ≢ a2
           end) /\
            (match r1 with 
             | None => fright a2 a1 a0 ≡ a1
             | Some a1' => fright a2 a1 a0 = a1' ∧ a1' ⊑[A1]  a1 /\ a1' ≢ a1
             end)
    end.


(** * AbstractionSetoid: Abstraction with an equality relation.  *)


(** Note: This not used for now. Maybe it is an interesting
    intermediate representation on the way to lattices.

   One of the main property that is allows stating is the injectivity
   of gamma, and thus it can be used to prove the unicity of a best
   abstraction.

   It may be interesting also to verify the "datatype" operations:
   e.g.  that compare is a total order, that to_int is injective, that
   equal corresponds to equality (or is at least compatible with
   gamma). These operations are needed by the OCaml implementation
   (and possibly here, with msets, too) *)

(** Equiv is a comparison on abstract elements. Normally it should
  be Leibniz equality, but this fails for elements containting proofs,
  so we use an equivalence here. It would also help if we used other
  definitions of equivalence, e.g. physical equality.

  Note that gamma may not be injective, and that the order may not be
  antysymmetric (e.g., multiple representations of bottom in intervals. *)

(** We only require equivalence to be compatible with γ. *)
Record abstraction_setoid_laws {C: Type} {A: abstraction C} `{!Gamma A} `{Equiv0:!Equiv A} := {
    as_proper :> Proper (Equiv0 ==> (⊆⊇)) (γ)
  }.
Existing Instance as_proper.


(* Structure abstraction_setoid C :=  *)
(*   BuildAbstractionSetoid { *)
(*       as_car :> Type; *)
(*       as_gamma: Gamma as_car C; *)
(*       as_equiv: Equiv as_car; *)
(*       as_laws: abstraction_setoid_laws as_car C *)
(*     }. *)
(* Arguments BuildAbstractionSetoid {_ _ _ _} _. *)
(* Arguments as_gamma {_} _. *)
(* Arguments as_equiv {_} _. *)
(* Global Hint Unfold as_gamma : unfold_gamma. *)
(* Global Notation "(≡[ A ])" := (@as_equiv _ A). *)
(* Global Notation "a1 ≡[ A ] a2" := (@as_equiv _ A a1 a2) (at level 70). *)

(* (* Locally infer notations from an abstraction. *) *)
(* Hint Extern 0 (Gamma _ _) => refine (@as_gamma _ _); shelve : typeclass_instances. *)
(* Hint Extern 0 (Equiv _) => refine (@as_equiv _ _); shelve : typeclass_instances. *)

(* Coercion abstraction_setoid_to_abstraction {C} (A:abstraction_setoid C) : abstraction C := *)
(*   BuildAbstraction (as_gamma A). *)
(* Canonical abstraction_setoid_to_abstraction. *)

(* Coercion abstraction_setoid_to_abstract_domain {C} (A:abstraction_setoid C) : abstract_domain C := *)
(*   BuildAbstractDomain (as_gamma A). *)
(* Canonical abstraction_setoid_to_abstraction. *)

(** * Tactics  *)
Ltac overapproximation_proof :=
  match goal with
  (** Introduce the two abstract elements, the three concrete elements, and their relation. *)
  | |- binary_overapproximation _ _ _ ?fA (collecting_binary_forward ?fC) =>
      move=> a2 a1 c0 [c2 [c1 [Hc2_in_a2 [Hc1_in_a1 Hc0]]]]
  | |- unary_overapproximation _ _ ?fA (collecting_forward ?fC) =>
      move=> a1 c0 [c1 [Hc1_in_a1 Hc0]]               
  end.



(** * Interface to the different modules. *)

(** Note that:

    1. Rocq generation of MLI mostly lists what is in an ML file;

    2. Making sure that things are encapsulated is really cumbersome
       (you have to explicitly define modules and check them with
       module types);

    3. we explicitly want to take advantage of some of the properties
       of the submodules that we use; and in general our goal is to
       provide the best function for a given abstraction; and thus, we
       cannot really encapsulate;

    4. Modules are not firstclass in Rocq; while we can convert a
       module into a packed class, we cannot do the opposite, and in
       particular we cannot pass a PackedClass as the argument to a
       functor.
   
   Thus here, we see module types as as a list "minimal requirements";
   we check that each module complies with this minimal requirements
   during extraction. The purepose of these modules is only extraction
   to suitable OCaml modules with nice interface; they are not used as
   an internal API. *)

(** An Abstract domain is extracted in just the datatype for the
    element, but in the theory it also contains the orders etc.

    Note: the packed class may be redundant here. *)
Module Type ABSTRACT_DOMAIN.
  Parameter t: Type.      (* The type of abstract elements. *)
  Parameter concr: Type.  (* The type of concrete elements. *)
  Parameter ad: abstract_domain concr.
  Axiom ad_car_ad_eq_t : ad_car ad = t.
  Parameter is_included: t -> t -> bool.
  (* Optional: printing function, quickcheck generators, implementation of gamma. *)
End ABSTRACT_DOMAIN.
