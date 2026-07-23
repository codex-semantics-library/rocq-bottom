(* OpsComp.v - Computational transfer functions for the Quadrivalent
   single-value abstraction: the forward boolean operations and their
   backward (refinement) counterparts. This is the executable core,
   destined to be extracted 1:1 to OCaml. Their proofs are in
   [OpsTheory.v].

   STATUS: negb, andb, orb, xorb, forward and backward (OpsTheory). *)

Require Import Quadrivalent.

(* Abstract negation function *)
Definition abs_negb (x:quadrivalent) : quadrivalent :=
  match x with
  | QBottom => QBottom
  | QFalse => QTrue
  | QTrue => QFalse
  | QTop => QTop
  end.

Definition backward_abs_negb (a1:quadrivalent) (a0:quadrivalent) : quadrivalent :=
  match a1,a0 with
  | _, QBottom => QBottom
  | a, QTop => a    
  | QBottom, _ => QBottom        (* Nothing to learn. *)
  | QTop, _ => abs_negb a0
  | QTrue, QFalse => QTrue
  | QFalse, QTrue => QFalse
  | _, _ => QBottom
  end.

Definition impl_backward_abs_negb (a1:quadrivalent) (a0:quadrivalent) : option quadrivalent :=
  match a1,a0 with
  | QBottom, _ => None
  | _, QTop => None
  | QTop, _ => Some (abs_negb a0)
  | QTrue, QFalse => None
  | QFalse, QTrue => None
  | _, _ => Some QBottom
  end.

(* Abstract AND function *)
Definition abs_andb (x y:quadrivalent) : quadrivalent :=
  match x,y with
  | QBottom, _ | _, QBottom => QBottom
  | QFalse, _ | _, QFalse => QFalse
  | QTrue, a | a, QTrue => a
  | QTop, QTop => QTop
  end.

Definition backward_abs_andb_left (a2 a1 a0:quadrivalent) : quadrivalent :=
  match a2, a1, a0 with
  | QBottom, _ , _ => QBottom
  | QFalse, _, QTrue => QBottom
  | QTrue, QTrue, QFalse => QBottom
  | QTrue, QFalse, QTrue => QBottom
  | _, QBottom, _ => QBottom                                                                       
  | _, _ , QBottom => QBottom
  | QTop, QFalse, QTrue => QBottom
  | QTop, QTrue, QFalse => QFalse
  | QTop, _, QTrue => QTrue
  | _, _, _ => a2
  end.

Definition backward_abs_andb_right a2 a1 a0 := backward_abs_andb_left a1 a2 a0.

Definition refine_bottom a := if Quadrivalent.eqb a QBottom then None else Some QBottom.
Definition refine_true a := if Quadrivalent.eqb a QTrue then None else Some QTrue.
Definition refine_false a := if Quadrivalent.eqb a QFalse then None else Some QFalse. 

Definition impl_backward_abs_andb (a2 a1 a0: quadrivalent): option quadrivalent * option quadrivalent :=
  match a2, a1, a0 with
  (** Detect impossible cases. *)
  | QBottom, _ , _ => (None, refine_bottom a1)
  | _, QBottom, _ => (Some QBottom, None)                                                                       
  | _, _ , QBottom => (Some QBottom, Some QBottom)
  | QFalse, _, QTrue => (Some QBottom, Some QBottom)
  | _, QFalse, QTrue => (Some QBottom, Some QBottom)                         
  | QTrue, QTrue, QFalse => (Some QBottom, Some QBottom)
  (** If result is true, both must be true. *)
  | _, _, QTrue => (refine_true a2, refine_true a1)
  (** Sometimes we learn that we have to be false. *)
  | QTop, QTrue, QFalse => (Some QFalse, None)
  | QTrue, QTop, QFalse => (None, Some QFalse)                            
  | _, _, _ => (None, None)
  end.

(* Abstract OR function *)
Definition abs_orb (x y:quadrivalent) : quadrivalent :=
  match x,y with
  | QBottom, _ | _, QBottom => QBottom
  | QTrue, _ | _, QTrue => QTrue
  | QFalse, a | a, QFalse => a
  | QTop, QTop => QTop
  end.

Definition backward_abs_orb_left (a2 a1 a0:quadrivalent) : quadrivalent :=
  match a2, a1, a0 with
  | QBottom, _ , _ => QBottom
  | QTrue, _, QFalse => QBottom
  | QFalse, QTrue, QFalse => QBottom
  | QFalse, QFalse, QTrue => QBottom
  | _, QBottom, _ => QBottom                                                                       
  | _, _ , QBottom => QBottom
  | QTop, QTrue, QFalse => QBottom
  | QTop, QFalse, QTrue => QTrue
  | QTop, _, QFalse => QFalse
  | _, _, _ => a2
  end.

Definition backward_abs_orb_right a2 a1 a0 := backward_abs_orb_left a1 a2 a0.

Definition impl_backward_abs_orb (a2 a1 a0: quadrivalent): option quadrivalent * option quadrivalent :=
  match a2, a1, a0 with
  (** Detect impossible cases. *)
  | QBottom, _ , _ => (None, refine_bottom a1)
  | _, QBottom, _ => (Some QBottom, None)                                                                       
  | _, _ , QBottom => (Some QBottom, Some QBottom)
  | QTrue, _, QFalse => (Some QBottom, Some QBottom)
  | _, QTrue, QFalse => (Some QBottom, Some QBottom)                         
  | QFalse, QFalse, QTrue => (Some QBottom, Some QBottom)
  (** If result is false, both must be false. *)
  | _, _, QFalse => (refine_false a2, refine_false a1)
  (** Sometimes we learn that we have to be true. *)
  | QTop, QFalse, QTrue => (Some QTrue, None)
  | QFalse, QTop, QTrue => (None, Some QTrue)                            
  | _, _, _ => (None, None)
  end.

(* Abstract XOR function *)
Definition abs_xorb (x y:quadrivalent) : quadrivalent :=
  match x,y with
  | QBottom, _ | _, QBottom => QBottom
  | QFalse, a | a, QFalse => a
  | QTrue, a | a, QTrue => abs_negb a
  | QTop, QTop => QTop
  end.

Definition backward_abs_xorb_left (a2 a1 a0:quadrivalent) : quadrivalent :=
  match a2, a1, a0 with
  | QBottom, _ , _ => a2
  | QTrue, QTrue, QTrue => QBottom
  | QTrue, QFalse, QFalse => QBottom                            
  | QFalse, QTrue, QFalse => QBottom
  | QFalse, QFalse, QTrue => QBottom                               
  | _, QBottom, _ => QBottom
  | _, _ , QBottom => QBottom
  | QTop, QTrue, QTrue => QFalse
  | QTop, QTrue, QFalse => QTrue
  | QTop, QFalse, QTrue => QTrue
  | QTop, QFalse, QFalse => QFalse
  | _, _, _ => a2
  end.

Definition backward_abs_xorb_right a2 a1 a0 := backward_abs_xorb_left a1 a2 a0.

Definition impl_backward_abs_xorb (a2 a1 a0:quadrivalent) :=
  match a2, a1, a0 with
  | QBottom, _ , _ => (None, refine_bottom a1)
  | _, QBottom, _ => (Some QBottom, None)                                                                       
  | _, _ , QBottom => (Some QBottom, Some QBottom)
  | QTrue, QTrue, QTrue => (Some QBottom, Some QBottom) 
  | QTrue, QFalse, QFalse => (Some QBottom, Some QBottom)
  | QFalse, QTrue, QFalse => (Some QBottom, Some QBottom)
  | QFalse, QFalse, QTrue => (Some QBottom, Some QBottom)
  | QTop, QTrue, QTrue => (Some QFalse, None)
  | QTop, QTrue, QFalse => (Some QTrue, None)
  | QTop, QFalse, QTrue => (Some QTrue, None)
  | QTop, QFalse, QFalse => (Some QFalse, None)
  | QTrue, QTop, QTrue => (None, Some QFalse)
  | QTrue, QTop, QFalse => (None, Some QTrue)
  | QFalse,QTop, QTrue => (None, Some QTrue)
  | QFalse,QTop, QFalse => (None, Some QFalse) 
  | _, _, _ => (None, None)
  end.

Module Boolean_Forward.
  Definition andb := abs_andb.
  Definition orb := abs_orb.
  Definition negb := abs_negb.
  Definition xorb := abs_xorb.      
End Boolean_Forward.

Module Boolean_Backward.
  Definition negb := impl_backward_abs_negb.  
  Definition andb := impl_backward_abs_andb.
  Definition orb := impl_backward_abs_orb.
  Definition xorb := impl_backward_abs_xorb.  
End Boolean_Backward.
