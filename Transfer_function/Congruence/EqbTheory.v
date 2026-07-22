(* EqbTheory.v - [Z.eqb] transfer function for the Congruence single-value
   abstraction: [cong_eqb] takes two congruences (r, m) and returns a
   [quadrivalent]. Split out of Congruence.v.

   The operations themselves live in [OpsComp.v]; this file is proofs only. *)

(* STATUS: eqb (Z.eqb): exact + best (cong_eqb_exact / cong_eqb_best). *)

Require Import Abstraction AbstractLattice.
Require Import ssreflect ssrbool ssrfun.
Require Import autoreflect.
Require Import Stdlib.Bool.Bool.
Require Import QuadrivalentTheory.
From Stdlib Require Import Lia. (* lia/nia; avoid Psatz which loads Reals axioms *)
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Congruence.
Require Import Transfer_function.Congruence.OpsComp.
Open Scope Z_scope.

Local Instance qv_exact_order : ExactOrder QuadrivalentTheory.qv.
Proof. move=> q1 q2. exact: qv_sqsubseteq_exact. Qed.

Lemma may_be_true_eqb_spec r1 m1 r2 m2 :
  may_be_true_eqb r1 m1 r2 m2 = true <->
  exists c2 c1, c2 ∈ γ[cong_ad] (r1, m1) /\
                c1 ∈ γ[cong_ad] (r2, m2) /\
                Z.eqb c2 c1 = true.
Proof.
  rewrite /may_be_true_eqb.
  case Hg : (Z.gcd m1 m2 =? 0).
  - move/Z.eqb_eq: Hg => Hg.
    have Hm1 := Z.gcd_eq_0_l _ _ Hg.
    have Hm2 := Z.gcd_eq_0_r _ _ Hg. subst m1 m2.
    split.
    + move/Z.eqb_eq => ->. exists r2, r2. split; [|split].
      * by apply/gamma_singleton.
      * by apply/gamma_singleton.
      * apply Z.eqb_refl.
    + move=> [c2 [c1 [Hc2 [Hc1 Heq]]]].
      move/gamma_singleton in Hc2.
      move/gamma_singleton in Hc1.
      rewrite Hc2 Hc1 in Heq.
      apply/Z.eqb_eq. by move/Z.eqb_eq: Heq.
  - move/Z.eqb_neq: Hg => Hg.
    rewrite Z.eqb_eq Z.mod_divide //. split.
    + move=> [q Hq].
      move: (Zis_gcd_bezout _ _ _ (Zgcd_is_gcd m1 m2)) => [u v Huv].
      exists (r1 + q * u * m1), (r1 + q * u * m1). split; [|split].
      * unfold_set. exists (q * u). lia.
      * unfold_set. exists (-(q * v)). nia.
      * apply Z.eqb_refl.
    + move=> [c2 [c1 [Hc2 [Hc1 Heq]]]].
      unfold_set in Hc2. move: Hc2 => [k2 Hk2].
      unfold_set in Hc1. move: Hc1 => [k1 Hk1].
      move/Z.eqb_eq: Heq => Heq.
      have Hr : r2 - r1 = k2 * m1 - k1 * m2 by lia.
      rewrite Hr. apply Z.divide_sub_r.
      * apply Z.divide_mul_r. apply Z.gcd_divide_l.
      * apply Z.divide_mul_r. apply Z.gcd_divide_r.
Qed.

Lemma may_be_false_eqb_spec r1 m1 r2 m2 :
  may_be_false_eqb r1 m1 r2 m2 = true <->
  exists c2 c1, c2 ∈ γ[cong_ad] (r1, m1) /\
                c1 ∈ γ[cong_ad] (r2, m2) /\
                Z.eqb c2 c1 = false.
Proof.
  rewrite /may_be_false_eqb. split.
  - case Hm1 : (m1 =? 0); case Hm2 : (m2 =? 0); rewrite /=.
    + (* m1 = 0, m2 = 0 : need r1 ≠ r2 *)
      move/negb_true_iff/Z.eqb_neq => Hne.
      move/Z.eqb_eq: Hm1 => Hm1z. subst m1.
      move/Z.eqb_eq: Hm2 => Hm2z. subst m2.
      exists r1, r2. split; [|split].
      * by apply/gamma_singleton.
      * by apply/gamma_singleton.
      * by apply/Z.eqb_neq.
    + (* m1 = 0, m2 ≠ 0 *)
      move=> _.
      move/Z.eqb_eq: Hm1 => Hm1z. move/Z.eqb_neq: Hm2 => Hm2nz. subst m1.
      have [c1 [Hc1 Hc1ge]] := cong_unbounded_above r2 m2 (r1 + 1) Hm2nz.
      exists r1, c1. split; [|split].
      * by apply/gamma_singleton.
      * exact Hc1.
      * apply/Z.eqb_neq. lia.
    + (* m1 ≠ 0, m2 = 0 *)
      move=> _.
      move/Z.eqb_neq: Hm1 => Hm1nz. move/Z.eqb_eq: Hm2 => Hm2z. subst m2.
      have [c2 [Hc2 Hc2ge]] := cong_unbounded_above r1 m1 (r2 + 1) Hm1nz.
      exists c2, r2. split; [|split].
      * exact Hc2.
      * by apply/gamma_singleton.
      * apply/Z.eqb_neq. lia.
    + (* m1 ≠ 0, m2 ≠ 0 *)
      move=> _.
      move/Z.eqb_neq: Hm1 => Hm1nz. move/Z.eqb_neq: Hm2 => Hm2nz.
      have [c2 [Hc2 _]] := cong_unbounded_above r1 m1 0 Hm1nz.
      have [c1 [Hc1 Hc1ge]] := cong_unbounded_above r2 m2 (c2 + 1) Hm2nz.
      exists c2, c1. split; [|split].
      * exact Hc2.
      * exact Hc1.
      * apply/Z.eqb_neq. lia.
  - move=> [c2 [c1 [Hc2 [Hc1 Heq]]]].
    case E : ((m1 =? 0) && (m2 =? 0) && (r1 =? r2)) => //.
    exfalso.
    move/andP: E => [/andP [Hm1 Hm2] Hr12].
    move/Z.eqb_eq: Hm1 => Hm1z. subst m1.
    move/Z.eqb_eq: Hm2 => Hm2z. subst m2.
    move/Z.eqb_eq: Hr12 => Hr12. subst r2.
    move/Z.eqb_neq: Heq => Hne.
    apply Hne.
    move/gamma_singleton :Hc2 => ->.
    move/gamma_singleton :Hc1 => ->.
    done.
Qed.

Lemma cong_eqb_exact r1 m1 r2 m2 :
  ExactlyRepresents (A:=QuadrivalentTheory.qv)
    (cong_eqb (r1, m1) (r2, m2))
    (collecting_binary_forward Z.eqb (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  rewrite /cong_eqb. apply: to_quadrivalent_exact.
  - rewrite may_be_true_eqb_spec. by [].
  - rewrite may_be_false_eqb_spec. by [].
Qed.

Lemma cong_eqb_best r1 m1 r2 m2 :
  BestAbstraction (A:=QuadrivalentTheory.qv)
    (cong_eqb (r1, m1) (r2, m2))
    (collecting_binary_forward Z.eqb (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  apply: is_alpha_is_best_abstraction.
  apply: exact_is_is_alpha. exact: cong_eqb_exact.
Qed.
