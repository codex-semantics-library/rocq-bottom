(* AddTheory.v - [Z.add] / [Z.opp] / [Z.sub] transfer functions for the
   Congruence single-value abstraction. The three are filed together because
   they are interdependent: [cong_sub] is [cong_add] composed with [cong_opp].
   Split out of Congruence.v. *)

(* STATUS: add (Z.add): sound + exact + α-complete
     (cong_add_sound / cong_add_exact / cong_add_alpha_complete);
   opp (Z.opp): exact (cong_opp_sound / cong_opp_exact);
   sub (Z.sub): exact (cong_sub_sound / cong_sub_exact). *)

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

(** * Addition operation. *)

(** γ(r1, m1) + γ(r2, m2) = γ(r1 + r2, gcd(m1, m2)).
    Sum of remainders gives the new remainder; gcd of moduli the new
    modulus — by Bezout, gcd(m1,m2)·Z = m1·Z + m2·Z. *)

Definition cong_add (a2 a1 : Z * Z) : Z * Z :=
  let (r2, m2) := a2 in
  let (r1, m1) := a1 in
  (r2 + r1, Z.gcd m2 m1).

Lemma cong_add_sound:
  binary_overapproximation cong_ad cong_ad cong_ad cong_add
    (collecting_binary_forward Z.add).
Proof.
  overapproximation_proof.
  move: a2 a1 Hc2_in_a2 Hc1_in_a1 => [ra ma] [rb mb] Ha Hb.
  unfold_set in *. move: Hc0 => <-.
  replace (c2 + c1 - (ra + rb)) with ((c2 - ra) + (c1 - rb)) by lia.
  apply Z.divide_add_r.
  - transitivity ma; [apply Z.gcd_divide_l | exact Ha].
  - transitivity mb; [apply Z.gcd_divide_r | exact Hb].
Qed.

(** Underapproximation: every c ∈ γ(r1+r2, gcd m1 m2) decomposes as
    c = c2 + c1 with c2 ∈ γ(r1,m1), c1 ∈ γ(r2,m2). The decomposition
    comes from Bezout's identity: gcd m1 m2 = u·m1 + v·m2. *)
Lemma cong_add_gamma_complete:
  binary_underapproximation cong_ad cong_ad cong_ad cong_add
    (collecting_binary_forward Z.add).
Proof.
  move=> [ra ma] [rb mb] c Hc.
  unfold_set in Hc. move: Hc => [k Hk].
  move: (Zis_gcd_bezout _ _ _ (Zgcd_is_gcd ma mb)) => [u v Huv].
  unfold_set.
  exists (ra + k * u * ma), (rb + k * v * mb). split; [|split].
  - exists (k * u). ring.
  - exists (k * v). ring.
  - nia.
Qed.

Lemma cong_add_exact:
  binary_exact cong_ad cong_ad cong_ad cong_add
    (collecting_binary_forward Z.add).
Proof.
  move=> a2 a1; split; [apply cong_add_gamma_complete|apply cong_add_sound].
Qed.

(** α-completeness of [cong_add]: if [c2] is the best abstraction of
    [S2] and [c1] of [S1], then [cong_add c2 c1] is the best abstraction
    of the collecting sum [S2 + S1]. Unlike intervals, no non-emptiness
    hypothesis on [S2], [S1] is needed: where witnesses are required the
    goal [order ...] is decidable, so we argue by contradiction and
    extract them via [alpha_non_empty] (see the first branch). *)
Lemma cong_add_alpha_complete (c2 c1 : Z * Z) (S2 S1 : ℘ Z) :
  binary_alpha_complete cong_ad cong_ad cong_ad cong_add
    (collecting_binary_forward Z.add) c2 c1 S2 S1.
Proof.
  rewrite /binary_alpha_complete => Ha2 Ha1 a.
  split.
  - (* T ⊆ γ a  ->  cong_add c2 c1 ⊑ a *)
    move: a => [r m] HT.
    (* The goal is [¬¬]-stable, so we may assume concrete witnesses
       s2 ∈ S2, s1 ∈ S1 (extracted via alpha_non_empty_witness). *)
    apply: (alpha_non_empty_witness c2 S2 Ha2) => -[s2 Hs2].
    apply: (alpha_non_empty_witness c1 S1 Ha1) => -[s1 Hs1].
    (* Every x ∈ S2 lands in γ(r - s1, m), via x + s1 ∈ T ⊆ γ(r,m). *)
    have HS2 : S2 ⊆ γ[cong_ad] (r - s1, m).
    { move=> x Hx.
      have Hxs1 : (x + s1) ∈ γ[cong_ad] (r, m) by apply HT; exists x, s1.
      unfold_set in Hxs1. move: Hxs1 => [k Hk]. by exists k; lia. }
    have HS1 : S1 ⊆ γ[cong_ad] (r - s2, m).
    { move=> x Hx.
      have Hs2x : (s2 + x) ∈ γ[cong_ad] (r, m) by apply HT; exists s2, x.
      unfold_set in Hs2x. move: Hs2x => [k Hk]. by exists k; lia. }
    have Hc2 := proj1 (Ha2 (r - s1, m)) HS2.
    have Hc1 := proj1 (Ha1 (r - s2, m)) HS1.
    have Hs2s1 : (s2 + s1) ∈ γ[cong_ad] (r, m) by apply HT; exists s2, s1.
    unfold_set in Hs2s1. move: Hs2s1 => [ks Hks].
    move: c2 c1 Ha2 Ha1 Hc2 Hc1 => [r2 m2] [r1 m1] _ _.
    rewrite /order /cong_add. move=> [Hm2 Hr2] [Hm1 Hr1]. split.
    + by apply Z.gcd_greatest.
    + replace (r2 + r1 - r)
        with ((r2 - (r - s1)) + (r1 - (r - s2)) - (s2 + s1 - r)) by lia.
      apply Z.divide_sub_r; first by apply Z.divide_add_r.
      by exists ks.
  - (* cong_add c2 c1 ⊑ a  ->  T ⊆ γ a *)
    move=> Hle x Hx.
    apply (ad_sqsubseteq_order_preserving cong_ad _ _ Hle).
    apply (cong_add_sound c2 c1).
    unfold_set in Hx. move: Hx => [x2 [x1 [Hx2 [Hx1 Hxeq]]]].
    exists x2, x1.
    split; first exact: proj2 (Ha2 c2) (reflexivity c2) x2 Hx2.
    split; first exact: proj2 (Ha1 c1) (reflexivity c1) x1 Hx1.
    exact Hxeq.
Qed.

(** * Negation. *)

(** -γ(r, m) = γ(-r, m); negation is exact on congruences. *)
Definition cong_opp (a : Z * Z) : Z * Z :=
  let (r, m) := a in (-r, m).

Lemma cong_opp_sound:
  unary_overapproximation cong_ad cong_ad cong_opp (collecting_forward Z.opp).
Proof.
  overapproximation_proof.
  move: a1 Hc1_in_a1 => [r m] Hc.
  unfold_set in *. move: Hc0 => <-.
  move: Hc => [k Hk]. exists (-k). lia.
Qed.

Lemma cong_opp_gamma_complete:
  unary_underapproximation cong_ad cong_ad cong_opp (collecting_forward Z.opp).
Proof.
  move=> [r m] c. unfold_set. move=> [k Hk].
  exists (-c). split; [|lia].
  exists (-k). lia.
Qed.

Lemma cong_opp_exact:
  unary_exact cong_ad cong_ad cong_opp (collecting_forward Z.opp).
Proof.
  move=> a; split; [apply cong_opp_gamma_complete|apply cong_opp_sound].
Qed.

(** * Subtraction. *)

(** Subtraction reduces to addition of the negation. *)
Definition cong_sub (a1 a2 : Z * Z) : Z * Z :=
  cong_add a1 (cong_opp a2).
(* MAYBE: an optimized version. *)

Lemma cong_sub_sound:
  binary_overapproximation cong_ad cong_ad cong_ad cong_sub
    (collecting_binary_forward Z.sub).
Proof.
  overapproximation_proof.
  rewrite /cong_sub. apply cong_add_sound.
  exists c2, (-c1). split; [|split]; [exact Hc2_in_a2 | | lia].
  apply cong_opp_sound. exists c1. split; [exact Hc1_in_a1 | reflexivity].
Qed.

Lemma cong_sub_gamma_complete:
  binary_underapproximation cong_ad cong_ad cong_ad cong_sub
    (collecting_binary_forward Z.sub).
Proof.
  move=> a2 a1 c Hc.
  have /= := cong_add_gamma_complete a2 (cong_opp a1) c Hc.
  unfold_set. move=> [c2 [co [Hc2 [Hco Heq]]]].
  have /= := cong_opp_gamma_complete a1 co Hco.
  unfold_set. move=> [c1 [Hc1 Hco1]].
  exists c2, c1. split; [|split]; [exact Hc2 | exact Hc1 | lia].
Qed.

Lemma cong_sub_exact:
  binary_exact cong_ad cong_ad cong_ad cong_sub
    (collecting_binary_forward Z.sub).
Proof.
  move=> a2 a1; split; [apply cong_sub_gamma_complete|apply cong_sub_sound].
Qed.
