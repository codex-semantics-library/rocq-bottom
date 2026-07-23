(* OpsComp.v - Computational transfer functions for the Congruence
   single-value abstraction. This is the executable core, destined to be
   extracted 1:1 to OCaml. Their proofs are in the matching [*Theory.v]
   files of this directory.

   STATUS: add, opp, sub (AddTheory), mul (MulTheory), div (DivTheory),
   quot (QuotTheory), le (LeTheory), eqb (EqbTheory). *)

From Stdlib Require Import ZArith Bool.
Require Import AbstractionCombination QuadrivalentComp.
Open Scope Z_scope.

(** * Z.add / Z.opp / Z.sub. See [AddTheory.v]. *)

(** γ(r1, m1) + γ(r2, m2) = γ(r1 + r2, gcd(m1, m2)).
    Sum of remainders gives the new remainder; gcd of moduli the new
    modulus — by Bezout, gcd(m1,m2)·Z = m1·Z + m2·Z. *)

Definition cong_add (a2 a1 : Z * Z) : Z * Z :=
  let (r2, m2) := a2 in
  let (r1, m1) := a1 in
  (r2 + r1, Z.gcd m2 m1).

(** -γ(r, m) = γ(-r, m); negation is exact on congruences. *)
Definition cong_opp (a : Z * Z) : Z * Z :=
  let (r, m) := a in (-r, m).

(** Subtraction reduces to addition of the negation. *)
Definition cong_sub (a1 a2 : Z * Z) : Z * Z :=
  cong_add a1 (cong_opp a2).
(* MAYBE: an optimized version. *)

(** * Z.mul. See [MulTheory.v]. *)

(** Granger's rule: (m1·Z + r1) · (m2·Z + r2) ⊆ gcd(r1·m2, r2·m1, m1·m2)·Z + r1·r2.
    Expanding c2·c1 − r1·r2 = r1·(c1−r2) + r2·(c2−r1) + (c2−r1)·(c1−r2)
    shows each summand is divisible by r1·m2, r2·m1, m1·m2 respectively,
    hence by their gcd.

    Note: multiplication is the best (smallest) enclosing congruence but
    is not γ-exact in general. E.g. γ(1,6)·γ(1,10) ⊊ γ(1,2) = odds,
    since 3 ∉ {(6k+1)(10l+1)} (no integer factorization of 3 has that
    form). So we prove soundness only. *)

Definition cong_mul (a1 a2 : Z * Z) : Z * Z :=
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  (r1 * r2, Z.gcd (Z.gcd (r1 * m2) (r2 * m1)) (m1 * m2)).

(** * Z.div (floor division). See [DivTheory.v]. *)

(** [cong_div] now returns a [WithBottom]-wrapped result so that the case
    where the divisor abstraction is exactly {0} (no valid divisor under
    the partial semantics) can be represented as [Bot]. *)
Definition cong_div (a1 a2 : Z * Z) : WithBottom.with_bottom (Z * Z) :=
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  if m2 =? 0 then
    if r2 =? 0 then WithBottom.Bot                          (* divisor_zero *)
    else if m1 mod r2 =? 0 then WithBottom.NotBot (r1 / r2, m1 / r2)  (* const_divides *)
    else WithBottom.NotBot (0, 1)                           (* const_pos/neg (top) *)
  else
    if (m1 =? 0) && (r1 =? 0) then WithBottom.NotBot (0, 0) (* dividend_zero *)
    else WithBottom.NotBot (0, 1).                          (* nonconstant_divisor (top) *)

(** * Z.quot (truncating division). See [QuotTheory.v]. *)

(** Contribution of a single arithmetic progression [d, d+step, d+2*step, ...]
    of divisor magnitudes (with [1 ≤ d], [1 ≤ step]) to the gcd of
    [ar / d'] over its terms [d' ≤ ar]:

    - if [d > ar]: no term in [[1, ar]], contribute [0] (gcd identity);
    - if [d ≤ ar < d + step]: a single term [d], contribute [ar / d];
    - if [d + step ≤ ar]: at least two terms; the gcd collapses to [1]
      (some term lies in [(ar/2, ar]] with quotient [1]). *)
Definition quot_gcd_progression (ar d step : Z) : Z :=
  if ar <? d then 0
  else if ar <? d + step then ar / d
  else 1.

(* Note: examples of interesting runs:
   10/3+8Z = 10/{-13,-5,3,11}.. = {0,-3,2,0} : gcd = 1.
   10/4+8Z = 10/{-12,-4,4,12}.. = {0,-2,2,0} : gcd = 2.
   10/2+30Z = 10/{-28,2,32}.. = {0,5,0} : gcd = 5. *)

(** GCD of all |r1|-div-|c| for nonzero c ∈ γ(r2, m2) with |c| ≤ |r1|.
    Returns 0 when no such c exists (D2a case). *)
Definition quot_gcd_compute (r1 r2 m2 : Z) : Z :=
  let ar := Z.abs r1 in
  let am := Z.abs m2 in
  let rm := r2 mod am in
  if rm =? 0 then
    quot_gcd_progression ar am am
  else
    (** This could be replaced by a case split:
        - Either one of the quot_gcd_progression is 0 (we take the other);
        - Otherwise, it returns a value in {1;2;3}, and the end result is 2
          only if both are 2. *)
    Z.gcd (quot_gcd_progression ar rm am)
          (quot_gcd_progression ar (am - rm) am).

Definition cong_quot (a1 a2 : Z * Z) : WithBottom.with_bottom (Z * Z) :=
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  if m2 =? 0 then
    if r2 =? 0 then WithBottom.Bot                                   (* divisor_zero *)
    else if (m1 =? 0) || ((m1 mod r2 =? 0) && (r1 mod r2 =? 0)) then
           WithBottom.NotBot (Z.quot r1 r2, Z.quot m1 r2)            (* const_divides *)
    else WithBottom.NotBot (0, 1)                                    (* top (const_pos/neg) *)
  else
    if m1 =? 0 then
      WithBottom.NotBot (0, quot_gcd_compute r1 r2 m2)               (* D2a / gcd case *)
    else WithBottom.NotBot (0, 1).                                   (* top (m1 ≠ 0) *)

(** * Z.leb. See [LeTheory.v]. *)

(** The result of [Z.leb a b] for [a ∈ γ(r1, m1)], [b ∈ γ(r2, m2)] is a
    set of booleans, abstracted by [quadrivalent]. When both inputs are
    constants ([m1 = 0 ∧ m2 = 0]), the comparison is exact: [Z.leb r1 r2].
    Otherwise at least one of γ(r1,m1), γ(r2,m2) is unbounded above and
    below, so both [true] and [false] are realised, giving [QTop] —
    again exact. *)

Definition cong_le (a1 a2 : Z * Z) : quadrivalent :=
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  if (m1 =? 0) && (m2 =? 0) then
    if r1 <=? r2 then QTrue else QFalse
  else QTop.

(** * Z.eqb. See [EqbTheory.v]. *)



(** [Z.eqb] returns [true] for some pair [(c2, c1) ∈ γ(r1,m1) × γ(r2,m2)]
    iff there exist k1, k2 with r1 + k1·m1 = r2 + k2·m2, equivalently
    [gcd(m1, m2) | (r2 - r1)].  Returning [false] is possible whenever at
    least one set has more than one element, i.e. unless both modulus are
    zero (constants) and the two constants coincide.  In all four
    combinations the result is exact. *)

Definition may_be_true_eqb (r1 m1 r2 m2 : Z) : bool :=
  let g := Z.gcd m1 m2 in
  if g =? 0 then r1 =? r2 else (r2 - r1) mod g =? 0.

Definition may_be_false_eqb (r1 m1 r2 m2 : Z) : bool :=
  negb ((m1 =? 0) && (m2 =? 0) && (r1 =? r2)).

Definition cong_eqb (a1 a2 : Z * Z) : quadrivalent :=
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  to_quadrivalent (may_be_true_eqb r1 m1 r2 m2) (may_be_false_eqb r1 m1 r2 m2).
