(* ZCongruenceComp.v - Computational core of the congruence abstraction
   (r, m) ↦ { z | m | z - r }. This is the executable core, destined to be
   extracted 1:1 to OCaml. Its proofs are in [ZCongruenceTheory.v].

   STATUS: join. *)

From Stdlib Require Import ZArith.
Open Scope Z_scope.

(** Carrier: the pair (r, m) denotes the class { z | m | z - r }. *)
Definition zcongruence := (Z * Z)%type.

(** Short name, for qualified use from other modules. *)
Definition t := zcongruence.

(** The join of two congruence classes γ(r1,m1) and γ(r2,m2) is the
    smallest congruence class containing both: (r1, gcd(gcd(m1,m2), r1-r2)).
    The modulus is the gcd of both moduli and the difference of remainders,
    and the remainder is r1 (arbitrary choice; r2 works equally). *)

Definition cong_join (a1 a2 : zcongruence) : zcongruence :=
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  (r1, Z.gcd (Z.gcd m1 m2) (r1 - r2)).
