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

(** [simpl] must not step past the non-zero obligation.  Rocq's [Z.quot x 0] is
    [0], OCaml's [Z.div x 0] raises, and [Hy] is the whole of what makes the
    extraction sound — so a proof that silently rewrites [quot_non_zero x y Hy]
    to [Z.quot x y] has dropped the only record of why the division is legal.
    Going through [quot_non_zero_quot] keeps that step explicit and greppable. *)
Arguments quot_non_zero : simpl never.

(** Floor and ceiling division, on the same bargain: the divisor's
    non-zeroness is a hypothesis rather than a guard, so each maps to a single
    zarith call ([Z.fdiv], [Z.cdiv]).

    Rocq's [Z.div] rounds toward minus infinity, so it i* the floor; the
    ceiling is [- ((- x) / y)], which is [⌈x/y⌉] at either sign of [y]. *)
Definition fdiv_non_zero (x y : Z) (Hy : y <> 0) : Z := Z.div x y.
Definition cdiv_non_zero (x y : Z) (Hy : y <> 0) : Z := - Z.div (- x) y.

Lemma fdiv_non_zero_div (x y : Z) (Hy : y <> 0) :
  fdiv_non_zero x y Hy = Z.div x y.
Proof. reflexivity. Qed.

Lemma cdiv_non_zero_div (x y : Z) (Hy : y <> 0) :
  cdiv_non_zero x y Hy = - Z.div (- x) y.
Proof. reflexivity. Qed.

Arguments fdiv_non_zero : simpl never.
Arguments cdiv_non_zero : simpl never.
