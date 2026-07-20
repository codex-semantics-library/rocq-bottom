Require Import Abstraction.
Require Import autoreflect.
From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Ring. (* bool_eq *)

Definition bool_eq := Ring.bool_eq.

(** A quadrivalent (4-valued logic) value exactly represents the
    powerset of {true,false} by isomorphism. Thus, every operation is
    exact, and we can prove it by computation. *)
Inductive quadrivalent :=
| QBottom
| QTrue
| QFalse
| QTop
.

Definition qv_gammab q b := 
  match q with
  | QBottom => false
  | QTop => true
  | QFalse => bool_eq b false
  | QTrue => bool_eq b true
  end.

Definition qv_gamma q : ℘ bool:=
  match q with
  | QBottom => ∅
  | QFalse => {[x | x = false]}
  | QTrue => {[x | x = true]}
  | QTop => {[ x | True ]}
  end.

Definition qv_abs : abstraction bool :=
  BuildAbstraction qv_gamma.

Instance qv_gammaP q b: AutoReflect(b ∈ γ[qv_abs] q)(qv_gammab q b).
Proof.
  case: q.
  all: apply: (iffP idP); unfold_set; by case: b.
Qed.


Global Hint Unfold qv_gamma qv_abs : unfold_gamma.
Local Instance qv_gamma_abs: Gamma qv_abs := γ[qv_abs].

(** We avoid giving a new name to equality, by simplicity. *)
Definition qv_setoidabsmixin : abstraction_setoid_laws (Gamma0:=qv_gamma_abs) (Equiv0:=(=)).
Proof.
  repeat constructor; subst; done.
Qed.

Definition qv_sqsubseteqb q1 q2 :=
  match q1,q2 with
  | QBottom, _ => true
  | _, QTop => true
  | QTrue, QTrue => true
  | QFalse,QFalse => true
  | _,_ => false
  end.

Instance qv_sqsubseteq: SqSubsetEq quadrivalent := qv_sqsubseteqb.
Instance qv_sqsubseteqP q1 q2: AutoReflect(q1 ⊑ q2)(qv_sqsubseteqb q1 q2).
Proof. 
  apply: (iffP idP); done.
Qed.


(** To make proofs easy, this is definitionally equal to the version
      that AutoReflect generates (simplified with simpl).

      Note that this method works well for booleans, but for other
      types, we probably want to do it more efficiently, e.g. by
      computing finite sets and using a set inclusion operation. *)
Definition boolset_subseteqb inPb inQb :=
  ((inPb false) ==> (inQb false))    
  && ((inPb true) ==> (inQb true)).

Instance AutoReflect_boolset_subseteq P inPb Q inQb:
  (forall (x:bool), AutoReflect(x ∈ P)(inPb x)) ->
  (forall (x:bool), AutoReflect(x ∈ Q)(inQb x)) ->
  AutoReflect(P ⊆ Q)(boolset_subseteqb inPb inQb).
Proof.
  (* have H: P ⊆ Q <-> (false ∈ P -> false ∈ Q) /\ (true ∈ P -> true ∈ Q). *)
  (* { unfold_set. split. *)
  (*   - move=> H. split; by apply: H. *)
  (*   - move=> [Hfalse Htrue] c. by case: c. *)
  (* }. *)
  move=> inPP inQP.
  (** Generate the boolean version from the spec automatically. *)
  (* eassert(Hr1:AutoReflect _ (boolset_subseteqb inPb inQb)) by apply _.     *)
  eassert(Hr2:AutoReflect (P ⊆ Q) _) by apply _.
  exact Hr2.
Qed.

Instance qv_sqsubseteq_gammaP q1 q2: AutoReflect(q1 ⊑γ q2)(qv_sqsubseteqb q1 q2).
Proof.
  (* to_set. *)
  evar (b:bool).
  (* We synthesize a decision procedure from the definition of q1 ⊑γ q2.  *)
  eassert(Hr:AutoReflect(γ q1 ⊆ γ q2) b) by apply _.
  (* Computationally, we check that it corresponds to qv_sqsubseteqb. *)
  assert(Hb:b = qv_sqsubseteqb q1 q2) by (destruct q1,q2; reflexivity).
  rewrite Hb in Hr. exact Hr.
Qed.

Lemma qv_sqsubseteq_exact q1 q2: q1 ⊑ q2 <-> q1 ⊑γ q2.
Proof.
  (* The boolean versions reflect both properties, so they are equal. *)
  have R1: reflect(q1 ⊑ q2)(qv_sqsubseteqb q1 q2) by apply qv_sqsubseteqP.
  have R2: reflect(q1 ⊑γ q2)(qv_sqsubseteqb q1 q2) by apply qv_sqsubseteq_gammaP.
  apply Bool.reflect_iff in R1.
  apply Bool.reflect_iff in R2.
  by rewrite R1 R2.
Qed.

Instance qv_sqsubseteq_preorder: @PreOrder quadrivalent (⊑).
Proof.
  (* No need for a case split here; we rely on the fact that ⊆ is
       already a preorder. *)
  constructor.
  - move => x. rewrite qv_sqsubseteq_exact. by to_set.
  - move => x y z. rewrite !qv_sqsubseteq_exact. to_set. by transitivity (γ y).
Qed.

Program Instance qv_admixin : abstract_domain_laws (A:=qv_abs) qv_gamma (⊑).
Next Obligation.
  to_set; apply qv_sqsubseteq_exact.
Defined.

(* Definition qv: abstraction bool := BuildAbstractDomain qv_admixin. *)
Definition qv: abstraction bool := BuildAbstractDomain qv_gamma qv_sqsubseteq qv_admixin.

Definition concr := bool.
Definition ad: abstract_domain concr := qv.
(* Definition t: Type := ad. *)
Definition t: Type := quadrivalent.
Lemma ad_car_ad_eq_t : ad_car ad = quadrivalent. Proof. reflexivity. Qed.


Lemma in_QTrue_iff b : b ∈ γ QTrue <-> b = true.
Proof. unfold_set; reflexivity. Qed.

Lemma in_QFalse_iff b : b ∈ γ QFalse <-> b = false .
Proof. unfold_set; reflexivity. Qed.

Lemma in_QBottom_iff b : b ∈ γ QBottom <-> False.
Proof. unfold_set; reflexivity. Qed.

Lemma in_QTop_iff b : b ∈ γ QTop <-> True.
Proof. unfold_set; reflexivity. Qed.

Lemma in_gamma_not_bottom (q : quadrivalent) (b : bool) :
  b ∈ γ[qv_abs] q -> q <> QBottom.
Proof. by destruct q; unfold_set. Qed.

Definition is_included := qv_sqsubseteqb.

(** * Conversion from may_be_true/may_be_false to quadrivalent. *)

Definition to_quadrivalent (may_true may_false : bool) : quadrivalent :=
  match may_true, may_false with
  | true, true => QTop
  | true, false => QTrue
  | false, true => QFalse
  | false, false => QBottom
  end.

Lemma to_quadrivalent_true may_true may_false :
  true ∈ γ[qv] (to_quadrivalent may_true may_false) <-> may_true = true.
Proof. case: may_true; case: may_false; unfold_set; intuition. Qed.

Lemma to_quadrivalent_false may_true may_false :
  false ∈ γ[qv] (to_quadrivalent may_true may_false) <-> may_false = true.
Proof. case: may_true; case: may_false; unfold_set; intuition. Qed.

(** Exactness criterion: [to_quadrivalent] is exact for any concrete set
    [S ⊆ {true, false}] whose realised values are described by the two
    booleans. *)
Lemma to_quadrivalent_exact (may_true may_false : bool) (S : ℘ bool) :
  (true ∈ S <-> may_true = true) ->
  (false ∈ S <-> may_false = true) ->
  ExactlyRepresents (A:=qv) (to_quadrivalent may_true may_false) S.
Proof.
  move=> HT HF. split. 
  - move=> b Hin. case: b Hin => Hin.
    + apply HT. by apply to_quadrivalent_true in Hin.
    + apply HF. by apply to_quadrivalent_false in Hin.
  - move=> b Hin. case: b Hin => Hin.
    + apply to_quadrivalent_true. by apply HT.
    + apply to_quadrivalent_false. by apply HF.
Qed.
