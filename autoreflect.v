From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import Ring. (* bool_eq *)
Require Import base. (* set operations. *)

(** This file can be used to synthesize boolean functions, propositions, or reflection proofs.  *)

  (** There are two uses of autoreflect:

      1. assert that a boolean program and a property match:
         [assert(AutoReflect (P ⊆ Q) (boolset_subseteqb inPb inQb)) by
         apply _].

         (for this to work, it is easier to generate a property or
         program and then prove that it is equal to the one we want).

      2. Generate a Prop corresponding to a boolean program:
         eassert(AutoReflect (_) (boolset_subseteqb inPb inQb)) by
         apply _.

         It then suffices to prove that the property corresponds to
         the specification we want.

      3. Generate a boolean program computing some property:
         eassert(AutoReflect (S ⊆ Q) _) by apply _.

         If the performance is satisfying, we have automatically
         generated a verified decision procedure.

         Note: the best way to debug issues it to try
         eassert(AutoReflect(prop) _) with smaller propositions, to
         find the piece that is not working. *)
  Class AutoReflect(P : Prop)(b: bool) := autoreflect:  reflect P b.

  Coercion autoreflect: AutoReflect >-> reflect.

  Instance AutoReflect_base(P : Prop)(b: bool) (H:reflect P b): AutoReflect P b.
  Proof. done. Qed.
  
  Instance AutoReflect_and P Q b1 b2
    `{AutoReflect P b1} `{AutoReflect Q b2} : AutoReflect (P /\ Q) (b1 && b2).
  Proof. apply: andPP; done. Qed.

  Instance AutoReflect_impl P Q b1 b2
    `{AutoReflect P b1} `{AutoReflect Q b2} : AutoReflect (P -> Q) (b1 ==> b2).
  Proof. apply: implyPP; done. Qed.

  Instance AutoReflect_iff P Q b1 b2
    `{HP:AutoReflect P b1} `{HQ:AutoReflect Q b2} : AutoReflect (P <-> Q) (bool_eq b1 b2).
  Proof.
    assert(H:(P -> Q) /\ (Q -> P) <-> (P <-> Q)) by tauto.
    apply: (equivP _ H).
    evar (b:bool).
    eassert(Hr:AutoReflect((P -> Q) /\ (Q -> P)) ?b) by apply _.
    assert(Hb:b = bool_eq b1 b2).
    { destruct b1, b2; reflexivity. }
    rewrite -Hb. apply Hr.
  Qed.

  Instance AutoReflect_elem_of_union (P: ℘ bool) inPb (Q: ℘ bool) inQb (b:bool):
    (AutoReflect(b ∈ P)(inPb b)) ->
    (AutoReflect(b ∈ Q)(inQb b)) ->
    (AutoReflect(b ∈ (P ∪ Q))(inPb b || inQb b)).
  Proof.
    move=> inPP inQP.
    apply: (iffP (orPP inPP inQP)); unfold_set.
  Qed.

  Instance AutoReflect_elem_of_intersection (P: ℘ bool) inPb (Q: ℘ bool) inQb (b:bool):
    (AutoReflect(b ∈ P)(inPb b)) ->
    (AutoReflect(b ∈ Q)(inQb b)) ->
    (AutoReflect(b ∈ (P ∩ Q))(inPb b && inQb b)).
  Proof.
    move=> inPP inQP.
    apply: (iffP (andPP inPP inQP)); unfold_set.
  Qed.

  (* Note: to avoid code duplication, we define the bool_all/bool_exists
     function, to avoid the generated term to explode in size.
     It makes the generated term easier to read. 

     However, this does not prevent the computation to increase
     exponentially in complexity: .g., with n binders, we have 2^n
     computations to make. *)  
  Definition bool_all (f : bool -> bool) : bool := f false && f true.

  Instance AutoReflect_forall_bool fP fb
    `{forall b:bool, (AutoReflect (fP b) (fb b))}:
    AutoReflect (forall b:bool, fP b) (bool_all fb).
  Proof.
    apply: (iffP idP).
    - move=> /andP [Hfalse Htrue] b.
      case b; by apply: H.
    - move => HP. apply/andP; split;by apply/H.
  Qed.

  Instance AutoReflect_set_unfold P P' b `{(AutoReflect P b)}:
    UnfoldSet P P' ->
    AutoReflect P' b.
  Proof.
    move=> Har.
    apply: (iffP H); firstorder.
  Qed.

  Definition bool_exists (f : bool -> bool) : bool := f false || f true.
  
  Instance AutoReflect_exists_bool fP fb
    `{forall b:bool, (AutoReflect (fP b) (fb b))}:
    AutoReflect (exists b:bool, fP b) (bool_exists fb).
  Proof.
    apply: (iffP idP).
    - move=> /orP [Hfalse | Htrue]; [exists false | exists true]; by apply: H.
    - move=> [b HP]. apply/orP. destruct b; [right|left];by apply/H.
  Qed.


  (* There is no reflection lemma on bool_eq in the standard library,
  so we put it here. *)
  Instance bool_eqP (b1 b2 : bool) : AutoReflect (b1 = b2) (bool_eq b1 b2).
  Proof.
    have bool_eq_dec: {b1 = b2} + {b1 <> b2} by decide equality.
    have bool_eq_spec: (bool_eq b1 b2) <-> b1 = b2. destruct b1, b2; firstorder.
    apply: (iffP idP); tauto.
  Qed.

(* Transform the current goal into a boolean formula using
autoreflect, and check that it is correct. *)
Ltac solve_with_autoreflect :=
  match goal with
  | |- ?G =>
      let k := fresh "k" in
      let Hr := fresh "Hr" in
      (* 1: Search for the boolean k that reflects the goal G *)        
      evar (k : bool);
      assert (Hr : AutoReflect G k) by apply _;
      (* Use reflection to turn the Prop goal into a boolean goal. *)
      apply: Hr;  
      reflexivity (* Solve by boolean reduction *)
  end.

(** Reflectable (currently not used) *)

(** The reflectable class correspond to propositions that can be
reflected using a boolan. *)
Class Reflectable (P : Prop) := {
  reflectb : bool;
  reflectP : reflect P reflectb
}.

(** A standard name for reflectable binary relations. *)
Class ReflectableRel {A B : Type} (rel : A -> B -> Prop) := {
  relb : A -> B -> bool;
  relP : forall x y, reflect (rel x y) (relb x y)
}.


(* Class ReflectableGamma {A C : Type} (gamma : A -> ℘ C) := { *)
(*   gammab : A -> C -> bool; *)
(*   gammaP : ∀ a c, reflect (c ∈ gamma a) (gammab a c) *)
(* }. *)

(* TODO: integrate autoreflect with quickcheck. *)
