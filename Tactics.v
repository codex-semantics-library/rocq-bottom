Require Import Abstraction.
(** This creates a database of all gamma functions.
    Then in proofs, we can autounfold with gamma_db
    to uncover all gammas. *)
Create HintDb gamma_db.
Hint Unfold γ: gamma_db.


(** Recursively destruct the conjonctions and existentials of an
    hypothesis, introducing new variables and hypothesis in the
    context. Try to give them useful name. *)
Ltac decompose_hypothesis H :=
  lazymatch type of H with
  | (exists x, ?P) => 
    let x' := fresh x in 
    destruct H as (x' & H); decompose_hypothesis H
  | _ /\ _ =>
      let H' := fresh H in
      let H'' := fresh H
      in destruct H as [H' H'']; decompose_hypothesis H'; decompose_hypothesis H''
  (* Rename tactics about variable x as Hx_in; if possible, Hx_in_γ; if possible Hx_in_γa
     (often, H in gamma) *)
  | ?c ∈ γ(?a2) =>
      let H' := fresh "H" c "_in" in
      first
        [ is_var a2;
          let H' := fresh "H" c "_in_γ_" a2 in
          rename H into H'
        | let H' := fresh "H" c "_in_γ" in
          rename H into H' ]
  | ?c ∈ ?S =>
      let H' := fresh "H" c "_in" in
      rename H into H'
  | _ => idtac
end.

(** Transform a goal of the form x \in [y | P y] into P x, and then
    simplify P x. *)
(* Ltac destruct_elem_of H := *)
(*   match type of H with *)
(*   | ?x ∈ ?S => rewrite elem_of_PropSet in H; decompose_hypothesis H *)
(*   end. *)
