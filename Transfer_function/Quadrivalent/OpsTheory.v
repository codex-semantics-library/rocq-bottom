Require Import Abstraction.
Require Import ssrbool ssreflect.
Require Import autoreflect.
Require Import QuadrivalentTheory.
Require Import Transfer_function.Quadrivalent.OpsComp.
Require Import Extraction.
Include QuadrivalentTheory.

(** Svaquadrivalent: extends a boolean lattice with boolean
    operations. All the operations are verified computationally,
    using boolean reflection of the Prop-predicates. *)
Module Concrete := Datatypes.

Lemma AutoReflect_unfold_set S P' b (c:bool) :
  AutoReflect (c ∈ S) b -> UnfoldSet (c ∈ S) P' -> AutoReflect P' b.
Proof.
  move=> Hr. case. move=> Hu. by apply: (equivP _ Hu).
Qed.
  
Global Hint Extern 0 (AutoReflect (_ ∈ _), _) =>
         class_apply AutoReflect_unfold_set : typeclass_instances.


(* TODO: use [Reflectable] (autoreflect.v) rather than [AutoReflect] here: the
   computation itself is irrelevant at this point. *)

(* Note: we could generalize to other decidable sets than (γ q). *)
Instance AutoReflect_collecting_forward (c:bool) f S1 inS1:
  (forall (x:bool), AutoReflect(x ∈ S1)(inS1 x)) ->
  AutoReflect(c ∈ collecting_forward f S1)
    (bool_exists (fun b => inS1 b && bool_eq (f b) c)).
Proof.
  move=> H1. rewrite /collecting_forward.
  (* We have to help a bit the instance search. *)
  eassert(AutoReflect(exists c1 : bool, c1 ∈ S1 /\ f c1 = c) _) by apply _.
  apply _.
Qed.

Instance AutoReflect_collecting_binary_forward (c0:bool) f  S2 inS2 S1 inS1:
  (forall (x:bool), AutoReflect(x ∈ S2)(inS2 x)) ->  
  (forall (x:bool), AutoReflect(x ∈ S1)(inS1 x)) ->
  AutoReflect(c0 ∈ collecting_binary_forward f S2 S1)
    (bool_exists (fun b : bool =>
                    bool_exists (fun b0 : bool =>
                                   [&& inS2 b, inS1 b0 & bool_eq (f b b0) c0] ))).
Proof.
  move=> H2 H1. rewrite /collecting_binary_forward.
  eassert(AutoReflect(exists c2 c1 : bool, c2 ∈ S2 /\ c1 ∈ S1 /\ f c2 c1 = c0) _) by apply _.
  apply _.
Qed.

Instance AutoReflect_collecting_backward (c:bool) f S1 inS1 S0 inS0:
  (forall (x:bool), AutoReflect(x ∈ S1)(inS1 x)) ->
  (forall (x:bool), AutoReflect(x ∈ S0)(inS0 x)) ->  
  AutoReflect(c ∈ collecting_backward f S1 S0)
    (bool_exists
       (fun b : bool => ([&& inS1 c, inS0 b & bool_eq (f c) b] ))).
Proof.
  move=> H1 H0.
  rewrite /collecting_backward.
  eassert(AutoReflect(exists c0 : bool, c ∈ S1 /\ c0 ∈ S0 /\ f c = c0) _) by apply _.
  apply _.
Qed.

Instance AutoReflect_collecting_binary_backward_left (c2:bool) f  S2 inS2 S1 inS1 S0 inS0:
  (forall (x:bool), AutoReflect(x ∈ S2)(inS2 x)) ->  
  (forall (x:bool), AutoReflect(x ∈ S1)(inS1 x)) ->
  (forall (x:bool), AutoReflect(x ∈ S0)(inS0 x)) ->
  AutoReflect(c2 ∈ collecting_binary_backward_left f S2 S1 S0)
    (bool_exists
       (fun b : bool => bool_exists (fun b0 : bool => [&& inS2 c2, inS1 b, inS0 b0 & bool_eq (f c2 b) b0] ))).
Proof.
  move=> H2 H1 H0. rewrite /collecting_binary_backward_left. 
  eassert(AutoReflect(exists c1 c0 : bool, c2 ∈ S2 /\ c1 ∈ S1 /\ c0 ∈ S0 /\ f c2 c1 = c0) _) by apply _.
  (* eassert(AutoReflect(c2 ∈ collecting_binary_backward_left f S2 S1 S0) _) by apply _. *)
  apply _.
Qed.


Instance AutoReflect_collecting_binary_backward_right (c1:bool) f  S2 inS2 S1 inS1 S0 inS0:
  (forall (x:bool), AutoReflect(x ∈ S2)(inS2 x)) ->  
  (forall (x:bool), AutoReflect(x ∈ S1)(inS1 x)) ->
  (forall (x:bool), AutoReflect(x ∈ S0)(inS0 x)) ->
  AutoReflect(c1 ∈ collecting_binary_backward_right f S2 S1 S0)
    (bool_exists
       (fun c2 : bool => bool_exists (fun c0 : bool => [&& inS2 c2, inS1 c1, inS0 c0 & bool_eq (f c2 c1) c0] ))).
Proof.
  move=> H2 H1 H0. rewrite /collecting_binary_backward_right.
  eassert(AutoReflect(exists c2 c0 : bool, c2 ∈ S2 /\ c1 ∈ S1 /\ c0 ∈ S0 /\ f c2 c1 = c0) _) by apply _.
  apply _.
Qed.




(** ** abs_negb *)

Lemma abs_negb_exact: unary_exact qv qv abs_negb
                        (collecting_forward Concrete.negb).
Proof.
  move=> q1.
  rewrite /ExactlyRepresents. unfold_set.
  move: q1.
  solve_with_autoreflect.
Qed.


Lemma backward_abs_negb_exact: binary_exact qv qv qv backward_abs_negb
                                 (collecting_backward Concrete.negb).
Proof.
  move=> a1 a0.
  rewrite /ExactlyRepresents. unfold_set.
  move: a1 a0.
  solve_with_autoreflect.
Qed.


(* Proof by "symbolic execution" on every path. *)
Tactic Notation "symbolic_run" :=
  repeat (
      match goal with
      (** If there is a match: try both branches, remember the branch we are in. *)
      | |- context [match ?x with _ => _ end] => destruct x eqn:?
      (** We cannot do this rewrite untill we have introduced the variables *)
      (* | |- context [_ ⊑γ _] => rewrite <- quadrivalent_sqsubseteq_iff *)
      (** injection is to simplify hypotheses like (None, Some q) = (None, Some p).  *)
      (** congruence is to reject hypotheses like Some true = Some false. *)
      | H: _ = _ |- _ => try injection H as H; try congruence; try subst
      end;
      simpl in *;
      try congruence;             (* Remove impossible cases. *)
      try done
    ).

Local Instance Equiv_eq : Equiv QuadrivalentTheory.t := (=).

Lemma impl_backward_abs_negb_correct: backward_unary_function_correct (A1:=qv) (A0:=qv) impl_backward_abs_negb backward_abs_negb.
Proof.
  (* (assert (H: bool_decide(backward_unary_function_correct impl_backward_abs_negb backward_abs_negb) = true)). *)
  intros a1 a0.
  (* unfold equiv, quadrivalent_equiv. *)
  destruct a1 eqn:Ha1, a0 eqn:Ha0; symbolic_run.
Qed.

(** Abstract and. *)

Lemma abs_andb_exact: binary_exact qv qv qv abs_andb
                        (collecting_binary_forward Concrete.andb).
Proof.
  move => a2 a1. to_set. move: a2 a1. solve_with_autoreflect.
Qed.

Lemma backward_abs_andb_left_exact:
  ternary_exact qv qv qv qv backward_abs_andb_left
    (collecting_binary_backward_left andb).
Proof.
  move=> a2 a1 a0. to_set. move: a2 a1 a0.
  solve_with_autoreflect.
Qed.

Lemma backward_abs_andb_right_exact:
  ternary_exact qv qv qv qv backward_abs_andb_right
    (collecting_binary_backward_right andb).
Proof.
  move=> a2 a1 a0. to_set. move: a2 a1 a0. solve_with_autoreflect.
Qed.    

Lemma impl_backward_abs_andb_correct: backward_binary_function_correct (A2:=qv) (A1:=qv) (A0:=qv) impl_backward_abs_andb backward_abs_andb_left backward_abs_andb_right.
Proof.
  intros a2 a1 a0.
  destruct a2 eqn:Ha2, a1 eqn:Ha1, a0 eqn:Ha0; symbolic_run; unfold refine_bottom in *; symbolic_run; solve_with_autoreflect.
Qed.









Lemma abs_orb_exact: binary_exact qv qv qv abs_orb
                       (collecting_binary_forward Concrete.orb).
Proof.
  move => a2 a1. to_set. move: a2 a1. solve_with_autoreflect.
Qed.

Lemma backward_abs_orb_left_exact:
  ternary_exact qv qv qv qv backward_abs_orb_left
    (collecting_binary_backward_left orb).
Proof.
  move=> a2 a1 a0. to_set. move: a2 a1 a0. solve_with_autoreflect.
Qed.    

Lemma backward_abs_orb_right_exact:
  ternary_exact qv qv qv qv backward_abs_orb_right
    (collecting_binary_backward_right orb).
Proof.
    move=> a2 a1 a0. to_set. move: a2 a1 a0. solve_with_autoreflect.
Qed.    



Lemma impl_backward_abs_orb_correct: backward_binary_function_correct (A2:=qv) (A1:=qv) (A0:=qv) impl_backward_abs_orb backward_abs_orb_left backward_abs_orb_right.
Proof.
  intros a2 a1 a0.
  destruct a2 eqn:Ha2, a1 eqn:Ha1, a0 eqn:Ha0; symbolic_run; unfold refine_bottom in *; symbolic_run.
Qed.

Lemma abs_xorb_exact: binary_exact qv qv qv abs_xorb
                        (collecting_binary_forward Concrete.xorb).
Proof.
  move => a2 a1. to_set. move: a2 a1. solve_with_autoreflect.
Qed.


Lemma backward_abs_xorb_left_exact:
  ternary_exact qv qv qv qv backward_abs_xorb_left
    (collecting_binary_backward_left xorb).
Proof.
    move=> a2 a1 a0. to_set. move: a2 a1 a0. solve_with_autoreflect.
Qed.    

Lemma backward_abs_xorb_right_exact:
  ternary_exact qv qv qv qv backward_abs_xorb_right
    (collecting_binary_backward_right xorb).
Proof.
  move=> a2 a1 a0. to_set. move: a2 a1 a0. solve_with_autoreflect.
Qed.    


Lemma impl_backward_abs_xorb_correct: backward_binary_function_correct (A2:=qv) (A1:=qv) (A0:=qv) impl_backward_abs_xorb backward_abs_xorb_left backward_abs_xorb_right.
Proof.
  intros a2 a1 a0.
  destruct a2 eqn:Ha2, a1 eqn:Ha1, a0 eqn:Ha0; symbolic_run; unfold refine_bottom in *; symbolic_run.
Qed.

