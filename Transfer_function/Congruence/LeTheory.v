(* LeTheory.v - [Z.leb] transfer function for the Congruence single-value
   abstraction: [cong_le] takes two congruences (r, m) and returns a
   [quadrivalent]. Split out of Congruence.v.

   The operations themselves live in [OpsComp.v]; this file is proofs only. *)

(* STATUS: le (Z.leb): exact + best (cong_le_exact / cong_le_best). *)

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

Lemma cong_le_exact r1 m1 r2 m2 :
  ExactlyRepresents (A:=QuadrivalentTheory.qv)
    (cong_le (r1, m1) (r2, m2))
    (collecting_binary_forward Z.leb (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  rewrite /cong_le.
  have HS_bool : forall b, b ∈ collecting_binary_forward Z.leb
                              (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)) ->
                            b = true \/ b = false.
  { move=> b _. by case: b; [left|right]. }
  case Hm1 : (m1 =? 0); case Hm2 : (m2 =? 0); rewrite /=.
  - (* m1 = 0 ∧ m2 = 0: γ(r1,0) = {r1}, γ(r2,0) = {r2}, S = {Z.leb r1 r2}. *)
    move/Z.eqb_eq: Hm1 => Hm1z. move/Z.eqb_eq: Hm2 => Hm2z. subst m1 m2.
    have Ha_eq : forall a, a ∈ γ[cong_ad] (r1, 0) -> a = r1
      by move=> a; exact (proj1 (gamma_singleton _ _)).
    have Hb_eq : forall b, b ∈ γ[cong_ad] (r2, 0) -> b = r2
      by move=> b; exact (proj1 (gamma_singleton _ _)).
    case Hcmp : (r1 <=? r2); split.
    + move=> b. rewrite in_QTrue_iff => ->.
      exists r1, r2. split; [|split].
      * by apply/gamma_singleton.
      * by apply/gamma_singleton.
      * by [].
    + move=> b [a [b' [Ha [Hb' Heq]]]].
      rewrite (Ha_eq _ Ha) (Hb_eq _ Hb') in Heq.
      rewrite in_QTrue_iff. by rewrite -Heq.
    + move=> b. rewrite in_QFalse_iff => ->.
      exists r1, r2. split; [|split].
      * by apply/gamma_singleton.
      * by apply/gamma_singleton.
      * by [].
    + move=> b [a [b' [Ha [Hb' Heq]]]].
      rewrite (Ha_eq _ Ha) (Hb_eq _ Hb') in Heq.
      rewrite in_QFalse_iff. by rewrite -Heq.
  - (* m1 = 0, m2 ≠ 0: γ(r1,0) = {r1}, γ(r2,m2) unbounded.  Result QTop, exact. *)
    move/Z.eqb_eq: Hm1 => Hm1z. move/Z.eqb_neq: Hm2 => Hm2nz. subst m1.
    split.
    + (* γ(QTop) ⊆ S: every bool is realised. *)
      move=> b _.
      case: b.
      * have [b' [Hb'_in Hb'_le]] := cong_unbounded_above r2 m2 r1 Hm2nz.
        exists r1, b'. split; [|split].
        -- by apply/gamma_singleton.
        -- exact: Hb'_in.
        -- by apply/Z.leb_le.
      * have [b' [Hb'_in Hb'_le]] := cong_unbounded_below r2 m2 (r1 - 1) Hm2nz.
        exists r1, b'. split; [|split].
        -- by apply/gamma_singleton.
        -- exact: Hb'_in.
        -- by apply/Z.leb_gt; lia.
    + by move=> b _; case: b.
  - (* m1 ≠ 0, m2 = 0. *)
    move/Z.eqb_neq: Hm1 => Hm1nz. move/Z.eqb_eq: Hm2 => Hm2z. subst m2.
    split.
    + move=> b _.
      case: b.
      * have [a [Ha_in Ha_le]] := cong_unbounded_below r1 m1 r2 Hm1nz.
        exists a, r2. split; [|split].
        -- exact: Ha_in.
        -- by apply/gamma_singleton.
        -- by apply/Z.leb_le.
      * have [a [Ha_in Ha_le]] := cong_unbounded_above r1 m1 (r2 + 1) Hm1nz.
        exists a, r2. split; [|split].
        -- exact: Ha_in.
        -- by apply/gamma_singleton.
        -- by apply/Z.leb_gt; lia.
    + by move=> b _; case: b.
  - (* m1 ≠ 0, m2 ≠ 0. *)
    move/Z.eqb_neq: Hm1 => Hm1nz. move/Z.eqb_neq: Hm2 => Hm2nz.
    split.
    + move=> b _.
      case: b.
      * have [a [Ha_in _]] := cong_unbounded_above r1 m1 0 Hm1nz.
        have [b' [Hb'_in Hb'_le]] := cong_unbounded_above r2 m2 a Hm2nz.
        exists a, b'. split; [|split].
        -- exact: Ha_in.
        -- exact: Hb'_in.
        -- by apply/Z.leb_le.
      * have [a [Ha_in _]] := cong_unbounded_above r1 m1 0 Hm1nz.
        have [b' [Hb'_in Hb'_le]] := cong_unbounded_below r2 m2 (a - 1) Hm2nz.
        exists a, b'. split; [|split].
        -- exact: Ha_in.
        -- exact: Hb'_in.
        -- by apply/Z.leb_gt; lia.
    + by move=> b _; case: b.
Qed.

Lemma cong_le_best r1 m1 r2 m2 :
  BestAbstraction (A:=QuadrivalentTheory.qv)
    (cong_le (r1, m1) (r2, m2))
    (collecting_binary_forward Z.leb (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  apply: is_alpha_is_best_abstraction.
  apply: exact_is_is_alpha. exact: cong_le_exact.
Qed.
