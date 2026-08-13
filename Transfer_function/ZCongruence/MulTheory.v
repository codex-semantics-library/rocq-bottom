(* MulTheory.v - [Z.mul] transfer function for the Congruence single-value
   abstraction: [cong_mul] takes two congruences (r, m) and returns a
   congruence. Split out of Congruence.v.

   The operations themselves live in [ZCongruenceOps.v]; this file is proofs only. *)

(* STATUS: mul (Z.mul): sound + α-complete + best, NOT γ-exact
   (cong_mul_sound / cong_mul_alpha_complete / cong_mul_best /
    cong_mul_not_gamma_exact). *)

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
Require Import ZCongruenceTheory.
Require Import Transfer_function.ZCongruence.ZCongruenceOps.
Open Scope Z_scope.
Generalizable All Variables.

(** * Multiplication. *)

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

(** * α-completeness of multiplication.

    Granger's rule gives the smallest congruence that overapproximates
    γ(r1,m1)·γ(r2,m2): for any (r', m') that contains this product set,
    (r1·r2, gcd(r1·m2, r2·m1, m1·m2)) ⊑ (r', m'). It is in fact
    α-complete, i.e. the same holds of the product of *arbitrary* sets
    S2, S1 that (r1,m1) and (r2,m2) are the best abstractions of;
    [cong_mul_best] then comes back by [binary_alpha_complete_to_binary_best].

    Pinned to concretizations, four "corner" products suffice — (r1,r2),
    (r1+m1,r2), (r1,r2+m2), (r1+m1,r2+m2) — their differences showing
    that m' divides each of r1·m2, m1·r2, m1·m2, hence their gcd.
    Corners are what an arbitrary S2 does not have: r1 + m1 need not
    belong to it. [cong_alpha_modulus_divide] below replaces them,
    recovering a divisibility of the *modulus* from one satisfied by
    every difference of elements — which is exactly what optimality of
    (r1,m1) says. *)

(** [m] divides [a·t] exactly when [m/gcd(m,t)] divides [a]: dividing out
    the common part leaves a factor coprime to [t/gcd(m,t)], which [Gauss]
    cancels. Both directions are needed below — the forward one turns a
    divisibility about products into a congruence bounding an operand set,
    the backward one turns the modulus divisibility that optimality hands
    back into a product one again. This is the gcd bookkeeping that
    [cong_alpha_affine_pullback] (QuotTheory.v) is stated so as to avoid;
    here there is no direction that avoids it. *)
Lemma Z_divide_mul_iff_div_gcd (m t a : Z) :
  t <> 0 -> ((m | a * t) <-> (m / Z.gcd m t | a)).
Proof.
  move=> Ht.
  have Hg : 0 < Z.gcd m t.
  { have Hnn := Z.gcd_nonneg m t.
    case: (Z.eq_dec (Z.gcd m t) 0) => [H0|Hne]; last lia.
    by move: (Z.gcd_eq_0_r _ _ H0). }
  have Hrp : rel_prime (m / Z.gcd m t) (t / Z.gcd m t)
    by apply/Zgcd_1_rel_prime; apply: Z.gcd_div_gcd; [lia | reflexivity].
  have Hm := Zdivide_Zdiv_eq _ _ Hg (Z.gcd_divide_l m t).
  have Htg := Zdivide_Zdiv_eq _ _ Hg (Z.gcd_divide_r m t).
  move: Hg Hrp Hm Htg. set g := Z.gcd m t. set m' := m / g. set t' := t / g.
  move=> Hg Hrp Hm Htg. rewrite Hm Htg. split.
  - move=> [k Hk]. apply: (Gauss _ t'); last exact: Hrp.
    exists k. by apply: (Z.mul_reg_l _ _ g); lia.
  - move=> [k Hk]. exists (k * t'). rewrite Hk. ring.
Qed.

(** From a divisibility satisfied by every difference [x - s] of elements
    of [S] scaled by [t], to the same divisibility on the modulus of the
    best congruence of [S]. The hypothesis says [S] sits inside the
    congruence of modulus [m/gcd(m,t)] around [s], and optimality of
    [(r,mm)] turns that into [m/gcd(m,t) | mm]. *)
Lemma cong_alpha_modulus_divide (r mm s t m : Z) (S : ℘ Z) :
  IsAlpha (A:=cong_ad) (r, mm) S -> s ∈ S ->
  (forall x, x ∈ S -> (m | (x - s) * t)) ->
  (m | mm * t).
Proof.
  move=> Ha Hs Hdiv.
  case: (Z.eq_dec t 0) => [->|Ht]; first by rewrite Z.mul_0_r; apply Z.divide_0_r.
  have HS : S ⊆ γ[cong_ad] (s, m / Z.gcd m t).
  { move=> x Hx. unfold_set.
    by apply/(Z_divide_mul_iff_div_gcd m t _ Ht); apply: Hdiv. }
  move: (proj1 (Ha (s, m / Z.gcd m t)) HS). rewrite /order => -[Hmod _].
  by apply/(Z_divide_mul_iff_div_gcd m t _ Ht).
Qed.

(** α-completeness proper. As in [cong_add_alpha_complete], no
    non-emptiness hypothesis on S2, S1 is needed: the goal [order ...] is
    decidable, so the two witnesses come from [alpha_non_empty_witness]. *)
Lemma cong_mul_alpha_complete (c2 c1 : Z * Z) (S2 S1 : ℘ Z) :
  binary_alpha_complete cong_ad cong_ad cong_ad cong_mul
    (collecting_binary_forward Z.mul) c2 c1 S2 S1.
Proof.
  rewrite /binary_alpha_complete => Ha2 Ha1 a.
  split.
  - (* T ⊆ γ a  ->  cong_mul c2 c1 ⊑ a *)
    move: a => [r m] HT.
    apply: (alpha_non_empty_witness c2 S2 Ha2) => -[s2 Hs2].
    apply: (alpha_non_empty_witness c1 S1 Ha1) => -[s1 Hs1].
    move: c2 c1 Ha2 Ha1 => [r1 m1] [r2 m2] Ha2 Ha1.
    (* Every product of an element of S2 by one of S1 lands in γ(r,m). *)
    have Hprod : forall x y, x ∈ S2 -> y ∈ S1 -> (m | x * y - r).
    { move=> x y Hx Hy.
      have Hxy : x * y ∈ γ[cong_ad] (r, m) by apply: HT; unfold_set; exists x, y.
      by unfold_set in Hxy. }
    (* Differences of two products, and of all four. *)
    have Hd2 : forall x, x ∈ S2 -> (m | (x - s2) * s1).
    { move=> x Hx. replace ((x - s2) * s1) with ((x * s1 - r) - (s2 * s1 - r))
        by ring.
      by apply: Z.divide_sub_r; apply: Hprod. }
    have Hd1 : forall y, y ∈ S1 -> (m | (y - s1) * s2).
    { move=> y Hy. replace ((y - s1) * s2) with ((s2 * y - r) - (s2 * s1 - r))
        by ring.
      by apply: Z.divide_sub_r; apply: Hprod. }
    have Hd21 : forall y, y ∈ S1 -> forall x, x ∈ S2 -> (m | (x - s2) * (y - s1)).
    { move=> y Hy x Hx.
      replace ((x - s2) * (y - s1))
        with (((x * y - r) - (x * s1 - r)) - ((s2 * y - r) - (s2 * s1 - r))) by ring.
      apply: Z.divide_sub_r; apply: Z.divide_sub_r; by apply: Hprod. }
    (* Optimality of (r1,m1) and (r2,m2) turns those into facts on the moduli. *)
    have Hm1s1 : (m | m1 * s1) by apply: (cong_alpha_modulus_divide _ _ _ _ _ _ Ha2 Hs2).
    have Hm2s2 : (m | m2 * s2) by apply: (cong_alpha_modulus_divide _ _ _ _ _ _ Ha1 Hs1).
    have Hm2m1 : (m | m2 * m1).
    { apply: (cong_alpha_modulus_divide _ _ _ _ _ _ Ha1 Hs1) => y Hy.
      rewrite Z.mul_comm.
      by apply: (cong_alpha_modulus_divide _ _ _ _ _ _ Ha2 Hs2) => x Hx;
         apply: Hd21. }
    (* Each witness is congruent to its residue, which moves s2, s1 to r1, r2. *)
    have [k2 Hk2] : (m1 | s2 - r1) by apply: (is_alpha_overapproximates _ _ Ha2).
    have [k1 Hk1] : (m2 | s1 - r2) by apply: (is_alpha_overapproximates _ _ Ha1).
    have Hr1m2 : (m | r1 * m2).
    { replace (r1 * m2) with (m2 * s2 - k2 * (m2 * m1)) by nia.
      apply: Z.divide_sub_r; first exact: Hm2s2.
      by apply: Z.divide_mul_r. }
    have Hr2m1 : (m | r2 * m1).
    { replace (r2 * m1) with (m1 * s1 - k1 * (m2 * m1)) by nia.
      apply: Z.divide_sub_r; first exact: Hm1s1.
      by apply: Z.divide_mul_r. }
    (* Conclude: (r1·r2, d) ⊑ (r, m) where d is the congruence gcd. *)
    rewrite /order /cong_mul. split.
    + apply: Z.gcd_greatest; last by rewrite Z.mul_comm.
      apply: Z.gcd_greatest; [exact: Hr1m2 | exact: Hr2m1].
    + replace (r1 * r2 - r)
        with ((s2 * s1 - r) - k2 * (r2 * m1) - k1 * (m2 * s2)) by nia.
      apply: Z.divide_sub_r; last by apply: Z.divide_mul_r.
      apply: Z.divide_sub_r; last by apply: Z.divide_mul_r.
      exact: Hprod.
  - (* cong_mul c2 c1 ⊑ a  ->  T ⊆ γ a *)
    move=> Hle x Hx.
    apply (ad_sqsubseteq_order_preserving cong_ad _ _ Hle).
    apply (cong_mul_sound c2 c1).
    unfold_set in Hx. move: Hx => [x2 [x1 [Hx2 [Hx1 Hxeq]]]].
    exists x2, x1.
    split; first exact: is_alpha_overapproximates _ _ Ha2 x2 Hx2.
    split; first exact: is_alpha_overapproximates _ _ Ha1 x1 Hx1.
    exact Hxeq.
Qed.

(** [cong_mul_best] is now the [γ]-pinned instance of the above:
    [cong_ad] has [ExactOrder], so every element is maximally reduced and
    [binary_alpha_complete_to_binary_best] applies. *)
Lemma cong_mul_best :
  binary_best cong_ad cong_ad cong_ad cong_mul
    (collecting_binary_forward Z.mul).
Proof.
  apply: binary_alpha_complete_to_binary_best.
  move=> a2 a1. exact: cong_mul_alpha_complete.
Qed.
