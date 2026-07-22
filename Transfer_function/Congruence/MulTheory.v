(* MulTheory.v - [Z.mul] transfer function for the Congruence single-value
   abstraction: [cong_mul] takes two congruences (r, m) and returns a
   congruence. Split out of Congruence.v. *)

(* STATUS: mul (Z.mul): sound + best, NOT γ-exact
   (cong_mul_sound / cong_mul_best / cong_mul_not_gamma_exact). *)

Require Import Abstraction AbstractLattice.
Require Import ssreflect ssrbool ssrfun.
Require Import BoundAbstraction.
Require Import AbstractionCombination.
Require Import BoundLattice.
Require Import autoreflect.
Require Import Tactics.
Require Import Stdlib.Bool.Bool.
Require Import Quadrivalent.
From Stdlib Require Import Lia. (* lia/nia; avoid Psatz which loads Reals axioms *)
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Congruence.
Open Scope Z_scope.
Generalizable All Variables.

(** * Multiplication. *)

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

(** Counterexample to exactness. [cong_mul (1,6) (1,10) = (1,2)], whose
    concretization γ(1,2) is the odd integers; yet 3 — though odd — is
    not a product of an element of γ(1,6) by an element of γ(1,10): that
    would require 3 = (6k+1)·(10l+1), but the only divisors of 3 are
    ±1, ±3, none of which is simultaneously ≡ 1 (mod 6) and ≡ 1 (mod 10).
    So non-exactness is a property of integer multiplication itself, not
    of [cong_mul]: the best enclosing congruence simply cannot be exact. *)
Lemma cong_mul_not_gamma_exact :
  ~ binary_exact cong_ad cong_ad cong_ad cong_mul
      (collecting_binary_forward Z.mul).
Proof.
  move=> Hex.
  have Hc0_in : (3 : Z) ∈ γ[cong_ad] (cong_mul (1, 6) (1, 10)).
  { rewrite /cong_mul. unfold_set. by exists 1. }
  (* Exactness forces 3 into the collecting product set of two odds. *)
  have Hin : (3 : Z) ∈ collecting_binary_forward Z.mul
               (γ[cong_ad] (1, 6)) (γ[cong_ad] (1, 10))
    by case: (Hex (1, 6) (1, 10)) => [Hsub _]; exact: (Hsub 3 Hc0_in).
  clear Hex Hc0_in.
  (* So c2 = 6·k2 + 1, c1 = 10·k1 + 1, with c2·c1 = 3. *)
  move: Hin; unfold_set; move=> -[c2 [c1 [[k2 Hk2] [[k1 Hk1] defc0]]]].
  (* c1 divides 3, so |c1| ≤ 3; enumerate the 7 candidates. *)
  have Hd : (c1 | 3) by exists c2; lia.
  have Hne : (3 : Z) <> 0 by lia.
  have Hb := Zdivide_bounds c1 3 Hd Hne.
  have Hcases : c1 = -3 \/ c1 = -2 \/ c1 = -1 \/ c1 = 0
                \/ c1 = 1 \/ c1 = 2 \/ c1 = 3 by lia.
  by case: Hcases => [Heq|[Heq|[Heq|[Heq|[Heq|[Heq|Heq]]]]]];
     rewrite Heq in defc0 Hk1; lia.
Qed.

Lemma cong_mul_sound:
  binary_overapproximation cong_ad cong_ad cong_ad cong_mul
    (collecting_binary_forward Z.mul).
Proof.
  overapproximation_proof.
  move: a2 a1 Hc2_in_a2 Hc1_in_a1 => [ra ma] [rb mb] Ha Hb.
  unfold_set in *. move: Hc0 => <-.
  move: Ha Hb => [ka Hka] [kb Hkb].
  replace (c2 * c1 - ra * rb)
    with (kb * (ra * mb) + ka * (rb * ma) + (ka * kb) * (ma * mb)) by nia.
  apply Z.divide_add_r; [apply Z.divide_add_r|].
  - apply Z.divide_mul_r. transitivity (Z.gcd (ra * mb) (rb * ma));
      [apply Z.gcd_divide_l | apply Z.gcd_divide_l].
  - apply Z.divide_mul_r. transitivity (Z.gcd (ra * mb) (rb * ma));
      [apply Z.gcd_divide_l | apply Z.gcd_divide_r].
  - apply Z.divide_mul_r. apply Z.gcd_divide_r.
Qed.

(** * Best abstraction for multiplication.

    Granger's rule gives the smallest congruence that overapproximates
    γ(r1,m1)·γ(r2,m2): for any (r', m') that contains this product set,
    (r1·r2, gcd(r1·m2, r2·m1, m1·m2)) ⊑ (r', m'). The proof feeds four
    "corner" products into the hypothesis — (r1,r2), (r1+m1,r2),
    (r1,r2+m2), (r1+m1,r2+m2) — and combines the resulting divisibility
    facts (differences of two, three, four corners) to show m' divides
    each of r1·m2, m1·r2, m1·m2, hence their gcd. *)

Lemma cong_mul_best :
  binary_best cong_ad cong_ad cong_ad cong_mul
    (collecting_binary_forward Z.mul).
Proof.
  move=> [r1 m1] [r2 m2]. split; first by apply: cong_mul_sound.
  move=> [r' m'] HS.
  (* Feeding any (c2, c1) in the two γ's into HS gives m' | c2*c1 - r'. *)
  have in_prod : forall c2 c1,
    c2 ∈ γ[cong_ad] (r1, m1) -> c1 ∈ γ[cong_ad] (r2, m2) ->
    (m' | c2 * c1 - r').
  { move=> c2 c1 H2 H1.
    have Hmem : c2 * c1 ∈ γ[cong_ad] (r', m').
    { apply: HS. unfold_set. by exists c2, c1. }
    by unfold_set in Hmem. }
  (* Four corner points of γ(r1,m1) × γ(r2,m2): *)
  have Hr1     : r1      ∈ γ[cong_ad] (r1, m1) by unfold_set; exists 0; lia.
  have Hr2     : r2      ∈ γ[cong_ad] (r2, m2) by unfold_set; exists 0; lia.
  have Hr1m1   : r1 + m1 ∈ γ[cong_ad] (r1, m1) by unfold_set; exists 1; lia.
  have Hr2m2   : r2 + m2 ∈ γ[cong_ad] (r2, m2) by unfold_set; exists 1; lia.
  have H00 := in_prod _ _ Hr1   Hr2.      (* m' | r1·r2 - r' *)
  have H10 := in_prod _ _ Hr1m1 Hr2.      (* m' | (r1+m1)·r2 - r' *)
  have H01 := in_prod _ _ Hr1   Hr2m2.    (* m' | r1·(r2+m2) - r' *)
  have H11 := in_prod _ _ Hr1m1 Hr2m2.    (* m' | (r1+m1)·(r2+m2) - r' *)
  (* Differences of corners isolate each term. *)
  have Hm1r2 : (m' | m1 * r2).
  { replace (m1 * r2) with ((r1 + m1) * r2 - r' - (r1 * r2 - r')) by ring.
    exact: Z.divide_sub_r H10 H00. }
  have Hr1m2 : (m' | r1 * m2).
  { replace (r1 * m2) with (r1 * (r2 + m2) - r' - (r1 * r2 - r')) by ring.
    exact: Z.divide_sub_r H01 H00. }
  have Hm1m2 : (m' | m1 * m2).
  { replace (m1 * m2)
      with ((r1 + m1) * (r2 + m2) - r' - (r1 * r2 - r') - m1 * r2 - r1 * m2)
      by ring.
    apply: Z.divide_sub_r; [|exact Hr1m2].
    apply: Z.divide_sub_r; [|exact Hm1r2].
    exact: Z.divide_sub_r H11 H00. }
  (* Conclude: (r1·r2, d) ⊑ (r', m') where d is the congruence gcd. *)
  split; last exact: H00.
  apply: Z.gcd_greatest; last exact: Hm1m2.
  apply: Z.gcd_greatest; first exact: Hr1m2.
  by rewrite Z.mul_comm.
Qed.
