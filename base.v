(** Base definitions and operations. *)
From Stdlib Require Import Utf8.
From Stdlib Require Export RelationClasses.
From Stdlib Require Import Relations.

Require Import ssreflect.

Declare Scope rocq_bottom_scope.
Open Scope rocq_bottom_scope.

(** * Subset type. *)
Notation "` x" := (proj1_sig x) (at level 10).


(** * Operational type classes in the style of stdpp/mathclasses.

See [Spitters&van der Weeger, Type Classes for Mathematics in Type
Theory, 2011] for an explanation of operational type classes. *)

Class Equiv A := equiv: relation A.
Global Hint Mode Equiv ! : typeclass_instances.
Infix "≡" := equiv (at level 70, no associativity) : rocq_bottom_scope.
Notation "(≡)" := equiv (only parsing) : rocq_bottom_scope.
Notation "(≢)" := (λ X Y, ¬X ≡ Y) (only parsing) : rocq_bottom_scope.
Notation "X ≢ Y":= (¬X ≡ Y) (at level 70, no associativity) : rocq_bottom_scope.
Class Inj {A B} (R : relation A) (S : relation B) (f : A → B) : Prop :=
  inj x y : S (f x) (f y) → R x y.

Notation "(=)" := eq (only parsing) : rocq_bottom_scope.

Class AntiSymm {A} (R S : relation A) : Prop :=
  anti_symm x y : S x y → S y x → R x y.

Class SqSubsetEq A := sqsubseteq: relation A.
Global Hint Mode SqSubsetEq ! : typeclass_instances.
Infix "⊑" := sqsubseteq (at level 70) : rocq_bottom_scope.
Notation "(⊑)" := sqsubseteq (only parsing) : rocq_bottom_scope.


(** * Double-negation stability.

A proposition is [Stable] when double negation can be eliminated for
it. Decidable propositions are stable; so is any negation. A stable
goal may be proved by contradiction and lets [¬¬X] hypotheses be used
as if [X] held (the [¬¬]-monad). *)
Class Stable (P : Prop) : Prop := stable : ¬ ¬ P → P.
Global Hint Mode Stable ! : typeclass_instances.

(** Decidability implies stability. *)
Definition dec_stable {P : Prop} (d : {P} + {¬ P}) : Stable P :=
  fun nnp => match d with
             | left p  => p
             | right np => match nnp np with end
             end.

(** A negation is always stable. *)
Global Instance stable_not (P : Prop) : Stable (¬ P) :=
  fun nnnp p => nnnp (fun np => np p).

(** [False] is stable (the base case). *)
Global Instance stable_False : Stable False :=
  fun nnf => nnf (fun f => f).

(** Stability is closed under conjunction. *)
Global Instance stable_and (P Q : Prop) :
  Stable P → Stable Q → Stable (P ∧ Q).
Proof.
  move=> SP SQ nnpq. split.
  - apply: SP => np. apply: nnpq => -[p _]. exact: np p.
  - apply: SQ => nq. apply: nnpq => -[_ q]. exact: nq q.
Qed.

(** Stability is closed under universal quantification (hence under
implication, taking [A := P]). *)
Global Instance stable_forall {A} (P : A → Prop) :
  (∀ x, Stable (P x)) → Stable (∀ x, P x).
Proof.
  move=> SP nnP x. apply: (SP x) => npx.
  apply: nnP => HP. exact: npx (HP x).
Qed.

(** Stability is closed under implication into a stable conclusion.
Derivable from [stable_forall], but stated explicitly since [→] is not
syntactically a [∀] for typeclass resolution. *)
Global Instance stable_impl (P Q : Prop) : Stable Q → Stable (P → Q).
Proof.
  move=> SQ nnPQ p. apply: SQ => nq.
  apply: nnPQ => HPQ. exact: nq (HPQ p).
Qed.

(** Stability is closed under bi-implication. *)
Global Instance stable_iff (P Q : Prop) :
  Stable P → Stable Q → Stable (P ↔ Q).
Proof.
  move=> SP SQ nnIff. split.
  - move=> p. apply: SQ => nq. apply: nnIff => -[pq _]. exact: nq (pq p).
  - move=> q. apply: SP => np. apply: nnIff => -[_ qp]. exact: np (qp q).
Qed.


(** * Sets and convenience utilities. *)

(** We put our set in a separate type to help automation. *)
Record propset (C : Type) : Type := PropSet { propset_car : C -> Prop }.
Add Printing Constructor propset.
Notation "'℘' C" := (propset C) (at level 0). (* \wp. *)
Global Arguments PropSet {_} _ : assert.
Global Arguments propset_car {_} _ _ (* / *) : assert.
Notation "{[ x | P ]}" := (PropSet (fun x => P))
  (at level 1, x as pattern, format "{[  x  |  P  ]}") : rocq_bottom_scope.


Definition propset_elem_of {C} (c:C) a := (propset_car a) c.
Arguments propset_elem_of {C} c a (* / *).

Infix "∈" := propset_elem_of (at level 70) : rocq_bottom_scope. (* \in. *)
Lemma propset_elem_of_iff {C} (c:C) f: c ∈ PropSet f <-> f c.
Proof. done. Qed.

Definition propset_emptyset {C} : propset C := {[ x | False ]}.
Notation "∅" := propset_emptyset.

Definition full_set {C} : propset C := {[ x | True ]}.

(* We make propset_elem_of (and propset_car) opaque to enfore module
   boundaries, and also because otherwise, unfold_set does not work.
   Thus, you have to use propset_elem_of (or propset_elem_of_iff) 

 *)
Global Opaque propset_elem_of.
Global Opaque propset_car.


Definition propset_union {C} (A:propset C) (B:propset C) := {[ c | (c ∈ A) ∨ (c ∈ B) ]}.
Infix "∪" := propset_union (at level 50) : rocq_bottom_scope. (* \union. *)
Notation "(∪)" := (propset_union) (only parsing) : rocq_bottom_scope.

Definition propset_intersection {C} (A:propset C) (B:propset C) := {[ c | (c ∈ A) ∧ (c ∈ B) ]}.
Infix "∩" := propset_intersection (at level 50) : rocq_bottom_scope. (* \intersection. *)
Notation "(∩)" := (propset_intersection) (only parsing) : rocq_bottom_scope.

Definition propset_subseteq {C} (A:propset C) (B:propset C) := forall c, c ∈ A -> c ∈ B.
Infix "⊆" := propset_subseteq (at level 70) : rocq_bottom_scope. (* \subseteq. *)
Notation "(⊆)" := (propset_subseteq) (only parsing) : rocq_bottom_scope.

Definition propset_equiv {C} (A:propset C) (B:propset C) := A ⊆ B ∧ B ⊆ A.
Infix "⊆⊇" := propset_equiv (at level 70) : rocq_bottom_scope. (* \subseteq\supseteq. *)
Notation "(⊆⊇)" := (propset_equiv) (only parsing) : rocq_bottom_scope.

Lemma propset_equiv_iff {C} (A B: propset C): A ⊆⊇ B <-> forall c, c ∈ A <-> c ∈ B.
Proof.
  rewrite /propset_equiv/propset_subseteq. 
  split.
  - move=> [H1 H2] c. split; by [move /H1|move /H2].
  - move=> H. split; by move=> c /H.
Qed.
    
Global Instance propset_subseteq_preorder {C:Type}: PreOrder (@propset_subseteq C).
Proof.
  rewrite /propset_subseteq.
  constructor.
  - by move=> S c.
  - by move=> x y z Hxy Hyz c/Hxy/Hyz.
Qed.
    
Global Instance propset_equiv_equivalence {C:Type}: Equivalence (@propset_equiv C).
Proof.
  rewrite /propset_equiv.
  constructor.
  - move=> A. split; reflexivity.
  - by move=> A B [HAB HBA].
  - move=> X Y Z [HXY HYX] [HYZ HZY]. split; by transitivity Y.
Qed.


(** * unfold_set rewriting. *)

(** We unfold set using type-directed synthesis of a rewrite rule, in
    the style of stdpp.  Compared to normal setoid_rewriting, it
    simplifies rewriting under binders (works even if there are no
    declared morphisms), and traverses the terms only once (avoids a
    quadratic blowup on large terms). This is possible because all it
    does is transform definitionally equal transformations using hnf.

    The basic idea is this one:

    - We use an UnfoldSet P Q type class that identifies pair of an
      expression P that should be rewritten in Q.

    - We recursively build UnfoldSet instances, saying how to rewrite
      P into Q in each case.

    - For the base case c ∈ S, we use UnfoldSetHnf, paired with a
      Hint Extern rule telling that it should apply hnf.
      This allows unfold_set S to work even if S is a complicated
      expression. *)

Class UnfoldSet (P Q : Prop) := { 
  unfold_set_rewrite : P <-> Q 
  }.
Global Arguments unfold_set_rewrite _ _ {_} : assert.
Global Hint Mode UnfoldSet + - : typeclass_instances.

(** Base case:  apply hnf to find a Propset instance. *)
Class UnfoldSetHnf (P Q : Prop) := { unfold_set_hnf : UnfoldSet P Q  }.
Global Hint Extern 0 (UnfoldSetHnf _ _) => hnf; constructor : typeclass_instances.

(** We use the forward lemmas for the hypothesis, and backward for the goal. *)
Definition unfold_set_forward {P Q} `{UnfoldSet P Q} : P → Q := proj1 (unfold_set_rewrite P Q).
Definition unfold_set_backward {P Q} `{UnfoldSet P Q} : Q → P := proj2 (unfold_set_rewrite P Q).

Global Tactic Notation "unfold_set" := apply unfold_set_backward; cbv beta.
Global Tactic Notation "unfold_set" "in" hyp(H) :=
  apply unfold_set_forward in H; cbv beta in H.

Ltac unfold_set_allH :=
  repeat match goal with
    | [ H: _ |- _ ] => progress(unfold_set in H)
  end.

Global Tactic Notation "unfold_set" "in" "*" := unfold_set_allH; unfold_set.

(* Base case: membership in a literal notation {[ x | P ]}. Use simplification to find it. *)
Global Instance unfold_set_PropSet {C} (P : C → Prop) c Q :
  UnfoldSetHnf (P c) Q → UnfoldSet (c ∈ PropSet P) Q.
Proof. intro H. constructor. apply H. Qed.

(* Fallback: if find nothing else, do not change it. *)
Global Instance unfold_set_id (P : Prop) : UnfoldSet P P | 1000.
Proof. by constructor. Qed.


(* Rewrite set operators. *)
Lemma unfold_set_subseteq {C} (S S': propset C) (Q Q': C -> Prop):
  (forall c, UnfoldSet (c ∈ S) (Q c)) ->
  (forall c, UnfoldSet (c ∈ S') (Q' c)) ->
  UnfoldSet(S ⊆ S')(∀ c, Q c -> Q' c).
Proof. move=> HQ HQ'. constructor. split.
  - move=> H c Hq. apply (HQ' c). apply H. apply (HQ c). exact Hq.
  - move=> H c Hc. apply (HQ' c). apply H. apply (HQ c). exact Hc.
Qed.
Global Hint Extern 0 (UnfoldSet (_ ⊆ _) _) =>
  class_apply unfold_set_subseteq : typeclass_instances.

Lemma unfold_set_equiv {C} (S S': propset C) (Q Q': C -> Prop):
  (forall c, UnfoldSet (c ∈ S) (Q c)) ->
  (forall c, UnfoldSet (c ∈ S') (Q' c)) ->
  UnfoldSet(S ⊆⊇ S')(∀ c, Q c <-> Q' c).
Proof. move=> HQ HQ'. constructor. split.
  - move=> [H1 H2] c. split.
    + move=> Hq. apply (HQ' c). apply H1. apply (HQ c). exact Hq.
    + move=> Hq'. apply (HQ c). apply H2. apply (HQ' c). exact Hq'.
  - move=> H. split; move=> c Hc.
    + apply (HQ' c). apply H. apply (HQ c). exact Hc.
    + apply (HQ c). apply (proj2 (H c)). apply (HQ' c). exact Hc.
Qed.
(* Do not apply this by default as this makes some proof hang. *)
(* Global Hint Extern 0 (UnfoldSet (_ ⊆⊇ _) _) => *)
(*   class_apply unfold_set_equiv : typeclass_instances. *)

(* When we want to unfold a ⊆⊇ statement. *)
Ltac unfold_set_equiv :=
  have HU := unfold_set_equiv; unfold_set.

Global Instance unfold_set_intersection {C} (S S': propset C) c Q Q':
  UnfoldSet (c ∈ S) Q -> UnfoldSet (c ∈ S') Q' ->
  UnfoldSet(c ∈ S ∩ S')(Q /\ Q').
Proof.
  move=> [HQ] [HQ']. constructor.
  pose proof (propset_elem_of_iff c (fun c => c ∈ S ∧ c ∈ S')) as H.
  change (propset_intersection S S') with (PropSet (fun c => c ∈ S ∧ c ∈ S')).
  tauto.
Qed.

Global Instance unfold_set_union {C} (S S': propset C) c Q Q':
  UnfoldSet (c ∈ S) Q -> UnfoldSet (c ∈ S') Q' ->
  UnfoldSet(c ∈ S ∪ S')(Q \/ Q').
Proof.
  move=> [HQ] [HQ']. constructor.
  pose proof (propset_elem_of_iff c (fun c => c ∈ S ∨ c ∈ S')) as H.
  change (propset_union S S') with (PropSet (fun c => c ∈ S ∨ c ∈ S')).
  tauto.
Qed.

(* Build an instance for every construction. *)
Lemma unfold_set_forall {A} (P P' : A → Prop) :
  (∀ c, UnfoldSet (P c) (P' c)) → UnfoldSet (forall c, P c) (forall c, P' c).
Proof. constructor. firstorder. Qed.
Global Hint Extern 0 (UnfoldSet (forall _, _) _) =>
  class_apply unfold_set_forall : typeclass_instances.


Lemma unfold_set_exists {A} (P P' : A → Prop) :
  (∀ c, UnfoldSet (P c) (P' c)) → UnfoldSet (exists c, P c) (exists c, P' c).
Proof. constructor. firstorder. Qed.
Global Hint Extern 0 (UnfoldSet (exists _, _) _) =>
  class_apply unfold_set_exists : typeclass_instances.

Lemma unfold_set_let {A} (P P' : A → Prop) c':
  (∀ c, UnfoldSet (P c) (P' c)) → UnfoldSet (let c := c' in P c) (let c := c' in P' c).
Proof. constructor. firstorder. Qed.
Global Hint Extern 0 (UnfoldSet (let _ := _ in _) _) =>
  class_apply unfold_set_let : typeclass_instances.

Lemma unfold_set_impl P Q P' Q' :
  UnfoldSet P P' → UnfoldSet Q Q' → UnfoldSet (P → Q) (P' → Q').
Proof. constructor. firstorder. Qed.
Global Hint Extern 0 (UnfoldSet (_ → _) _) =>
  class_apply unfold_set_impl : typeclass_instances.

Lemma unfold_set_iff P Q P' Q' :
  UnfoldSet P P' -> UnfoldSet Q Q' -> UnfoldSet (P <-> Q) (P' <-> Q').
Proof. constructor. firstorder. Qed.
Global Hint Extern 0 (UnfoldSet (_ <-> _) _) =>
  class_apply unfold_set_iff : typeclass_instances.

Lemma unfold_set_and P Q P' Q' :
  UnfoldSet P P' -> UnfoldSet Q Q' -> UnfoldSet (P /\ Q) (P' /\ Q').
Proof. constructor. firstorder. Qed.
Global Hint Extern 0 (UnfoldSet (_ /\ _) _) =>
  class_apply unfold_set_and : typeclass_instances.

Lemma unfold_set_or P Q P' Q' :
  UnfoldSet P P' -> UnfoldSet Q Q' -> UnfoldSet (P \/ Q) (P' \/ Q').
Proof. constructor. firstorder. Qed.
Global Hint Extern 0 (UnfoldSet (_ \/ _) _) =>
  class_apply unfold_set_or : typeclass_instances.

Lemma unfold_set_not P P' :
  UnfoldSet P P' -> UnfoldSet (~P) (~P').
Proof. constructor. firstorder. Qed.
Global Hint Extern 0 (UnfoldSet (~ _) _) =>
  class_apply unfold_set_not : typeclass_instances.

(* Lemma unfold_set_reflect P Q P': *)
(*   UnfoldSet P P' -> UnfoldSet (reflect P Q) (reflect P' Q). *)
(* Proof. constructor. firstorder. Qed. *)
(* Global Hint Extern 0 (UnfoldSet (_ <-> _) _) => *)
(*   class_apply unfold_set_iff : typeclass_instances. *)


(* This lemma is useful to prove
     { x | exists y,z, P } ⊆⊇ { x | exists y,z, Q }

     by rewriting, instead of double implication (this does not always work,
     but it is a common subcase).

     It suffices to do: 
     { unfold_set_equiv. move=> x. apply: exists_iff => y. apply: exists_iff => z /=. rewrite H. done. } *)
Lemma exists_iff {A : Type} {P Q : A -> Prop} :
  (forall x, P x <-> Q x) ->
  (exists x, P x) <-> (exists x, Q x).
Proof.
  move=> HPQ.
  split; move=> [x Hx]; exists x; by apply (HPQ x).
Qed.

(* TODO: generalise [exists_iff_opp] and hoist it here. It currently exists as a
   Z-specific [Local Lemma] in Z_interval.v: "exists x" on the left corresponds to
   "exists -x" on the right, which is what aligns the witnesses when lifting
   positive operations to negative ones, in div and mult. The general form would be
   exists_iff modulo a (involutive?) transformation. *)
(* Lemma exists_iff_f {A : Type} {P Q : A -> Prop} (f:A -> A) {Hfinvo: forall x:A, f (f x) = x}: *)
(*   (forall x, P x <-> Q (f x)) -> *)
(*   (exists x, P x) <-> (exists x, Q (f x)). *)
(* Proof. *)
(*   move=> HPQ. *)
(*   split; move=> [x Hx]; exists (f x); by apply (HPQ x). *)
(* Qed. *)
