(* KnownBitsComp.v - Computational core of the known-bits abstraction: the
   [must0_must1] carrier, its non-bottom subset type, the [testbit] /
   [setbit_to] toolkit and the computational lattice operations. This is the
   executable core, destined to be extracted 1:1 to OCaml. Its proofs are in
   [KnownBitsTheory.v]. *)

Require Import QuadrivalentComp.
Require Import Stdlib.ZArith.ZArith.
Open Scope Z_scope.

Record must0_must1 := {
  must0 : Z;
  must1 : Z
}.

Definition testbit v (i : nat) : bool := Z.testbit v (Z.of_nat i).

(* Not [Local]: [Transfer_function/KnownBits/AddSubTheory.v] builds its
   bit-realization witnesses with it. *)
Definition setbit_to (v : Z) (i : nat) (b : bool) : Z :=
  if b then Z.setbit v (Z.of_nat i)
  else Z.clearbit v (Z.of_nat i).

Definition kb_testbit (kb : must0_must1) (i : nat) : quadrivalent :=
  match testbit (must0 kb) i, testbit (must1 kb) i with
  | false, false => QFalse
  | true,  true  => QTrue
  | false, true  => QBottom
  | true,  false => QTop
  end.

Definition kb_top : must0_must1 := {| must0 := -1; must1 := 0 |}.
Definition kb_bottom : must0_must1 := {| must0 := 0; must1 := -1 |}.

Definition kb_join (kb1 kb2 : must0_must1) : must0_must1 :=
  {| must0 := Z.lor (must0 kb1) (must0 kb2);
     must1 := Z.land (must1 kb1) (must1 kb2) |}.

Definition kb_meet (kb1 kb2 : must0_must1) : must0_must1 :=
  {| must0 := Z.land (must0 kb1) (must0 kb2);
     must1 := Z.lor (must1 kb1) (must1 kb2) |}.

Definition kb_non_bottom (kb : must0_must1) : Prop :=
  forall i : nat, kb_testbit kb i <> QBottom.

(** When the argument is non-bottom, then we can now the unknown bits
    by a xor of both arguments.  *)
Definition unknown_bits (kb : must0_must1) : Z :=
  Z.lxor (must0 kb) (must1 kb).

Definition nb_must0_must1 : Type := { kb : must0_must1 | kb_non_bottom kb }.
