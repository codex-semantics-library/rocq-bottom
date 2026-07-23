(* OpsComp.v - Computational transfer functions for the KnownBits
   single-value abstraction. This is the executable core, destined to be
   extracted 1:1 to OCaml. Their proofs are in the matching [*Theory.v]
   files of this directory.

   STATUS: lor, land, lxor (BitwiseTheory), add, sub (AddSubTheory). *)

From Stdlib Require Import ZArith.
Require Import KnownBits.

Open Scope Z_scope.

(** * Z.lor, Z.land, Z.lxor. See [BitwiseTheory.v]. *)

Definition kb_lor (kb1 kb2 : must0_must1) : must0_must1 :=
  {| must0 := Z.lor (must0 kb1) (must0 kb2);
     must1 := Z.lor (must1 kb1) (must1 kb2) |}.

Definition kb_land (kb1 kb2 : must0_must1) : must0_must1 :=
  {| must0 := Z.land (must0 kb1) (must0 kb2);
     must1 := Z.land (must1 kb1) (must1 kb2) |}.

Definition kb_lxor (kb1 kb2 : must0_must1) : must0_must1 :=
  let xor00 := Z.lxor (must0 kb1) (must0 kb2) in
  let xor11 := Z.lxor (must1 kb1) (must1 kb2) in
  let unknown := Z.lxor (must0 kb1) (must1 kb1) in
  {| must0 := Z.lor (Z.lor xor00 xor11) unknown;
     must1 := Z.land xor00 xor11 |}.

(** * Z.add and Z.sub. See [AddSubTheory.v]. *)

(** *** Closed-form [kb_add] — Vishwanathan et al., Listing 1, p.258.

    The kernel's [tnum_add] in σ-decomposed form: combine value sums
    and mask sums into a single carry expression, and read off the
    result tnum. The variable naming (sv, sm, sigma, chi, eta, rv)
    matches the paper exactly. *)
Definition kb_add (kb1 kb2 : must0_must1) : must0_must1 :=
  let v1    := must1 kb1 in
  let m1    := unknown_bits kb1 in
  let v2    := must1 kb2 in
  let m2    := unknown_bits kb2 in
  let sv    := (v1 + v2)%Z in
  let sm    := (m1 + m2)%Z in
  let sigma := (sv + sm)%Z in
  let chi   := Z.lxor sigma sv in
  let eta   := Z.lor chi (Z.lor m1 m2) in
  let rv    := Z.land sv (Z.lnot eta) in
  {| must1 := rv;
     must0 := Z.lor rv eta |}.

(** *** Closed-form [kb_sub] — Vishwanathan et al., §III-B sketch.

    The closed form follows the same σ-decomposition pattern as [kb_add]:
    [dv = must1 kb1 - must0 kb2] (minimum of γ subtraction),
    [dm = unknown_bits kb1 + unknown_bits kb2] (unknown-bit contributions),
    [σ = dv + dm], then [χ = σ ⊕ dv], [η = χ | m1 | m2], and the
    result [must1 = dv & ~η], [must0 = rv | η].

    The paper's [tnum_sub] is in the extended technical report; the
    body here matches the same σ/χ/η template as [tnum_add] (Listing 1)
    with [sv] replaced by [dv] (min of γ subtraction). *)

Definition kb_sub (kb1 kb2 : must0_must1) : must0_must1 :=
  let v1    := must1 kb1 in let m1 := unknown_bits kb1 in
  let v2    := must1 kb2 in let m2 := unknown_bits kb2 in
  let dv    := (v1 - must0 kb2)%Z in
  let dm    := (m1 + m2)%Z in
  let sigma := (dv + dm)%Z in
  let chi   := Z.lxor sigma dv in
  let eta   := Z.lor chi (Z.lor m1 m2) in
  let rv    := Z.land dv (Z.lnot eta) in
  {| must1 := rv;
     must0 := Z.lor rv eta |}.
