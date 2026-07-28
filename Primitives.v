(* Primitives.v - Additional Rocq operations, directly mapping to native OCaml
primitives. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

(** Truncated (C99) division as the partial function it is in OCaml: the
    proof erases, so this extracts to zarith's [Z.div] itself, rather than
    to a guard standing in for Rocq's [Z.quot x 0 = 0]. *)
Definition quot_non_zero (x y : Z) (Hy : y <> 0) : Z := Z.quot x y.

Lemma quot_non_zero_quot (x y : Z) (Hy : y <> 0) :
  quot_non_zero x y Hy = Z.quot x y.
Proof. reflexivity. Qed.
