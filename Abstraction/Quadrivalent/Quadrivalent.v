(* Quadrivalent.v - Computational core of the quadrivalent (4-valued
   logic) abstraction of booleans: the carrier, the inclusion test, the
   lattice operations and the decidable equalities. This is the executable
   core, destined to be extracted 1:1 to OCaml. Its proofs are in
   [QuadrivalentTheory.v]. *)

(** A quadrivalent (4-valued logic) value exactly represents the
    powerset of {true,false} by isomorphism. Thus, every operation is
    exact, and we can prove it by computation. *)
Inductive quadrivalent :=
| QBottom
| QTrue
| QFalse
| QTop
.

(* Definition t: Type := ad. *)
Definition t: Type := quadrivalent.

Definition qv_sqsubseteqb q1 q2 :=
  match q1,q2 with
  | QBottom, _ => true
  | _, QTop => true
  | QTrue, QTrue => true
  | QFalse,QFalse => true
  | _,_ => false
  end.

Definition is_included := qv_sqsubseteqb.

(** * Conversion from may_be_true/may_be_false to quadrivalent. *)

Definition to_quadrivalent (may_true may_false : bool) : quadrivalent :=
  match may_true, may_false with
  | true, true => QTop
  | true, false => QTrue
  | false, true => QFalse
  | false, false => QBottom
  end.

(** * Decidable equality. *)

Definition dec (q1 q2 : quadrivalent) : {q1 = q2} + {q1 <> q2}.
Proof. decide equality. Defined.

Definition eqb q1 q2 := if dec q1 q2 then true else false.

Definition equal := eqb.

(** Simple decidable equality: a direct pattern match that reduces
    even when the arguments are symbolic [match] expressions.
    Unlike [eqb], this avoids the [decide equality] complexity
    that blocks [solve_with_autoreflect]. *)
Definition qv_eqb (q1 q2 : quadrivalent) : bool :=
  match q1, q2 with
  | QBottom, QBottom => true
  | QTrue, QTrue => true
  | QFalse, QFalse => true
  | QTop, QTop => true
  | _, _ => false
  end.

(** * Lattice operations. *)

Definition join (x y:quadrivalent) : quadrivalent :=
  match x,y with
  | QTop, _ | _, QTop => QTop    
  | QBottom, a | a, QBottom => a
  | QTrue, QTrue => QTrue
  | QFalse, QFalse => QFalse
  | QTrue, QFalse | QFalse, QTrue => QTop
  end.

Definition meet (x y:quadrivalent) : quadrivalent :=
  match x,y with
  | QBottom, _ | _, QBottom => QBottom
  | QTop, a | a, QTop => a
  | QTrue, QTrue => QTrue
  | QFalse, QFalse => QFalse
  | QTrue, QFalse | QFalse, QTrue => QBottom
  end.
