(* QuotTheory.v - [Z.quot] (truncating division) transfer function for the
   Congruence single-value abstraction: [cong_quot] takes two congruences
   (r, m) and returns a congruence. Split out of Congruence.v.

   The operations themselves live in [OpsComp.v]; this file is proofs only. *)

(* STATUS: quot (Z.quot): sound + best (cong_quot_sound / cong_quot_best).
   Not γ-exact in general: the concrete quotient set of a progression is
   not itself a progression. *)

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
Require Import Transfer_function.Congruence.OpsComp.
Open Scope Z_scope.
Generalizable All Variables.

(** * Truncating division [Z.quot].

    [Z.quot] (rounding toward zero, C-style) differs from [Z.div]
    (floor, rounds toward −∞) near zero. For [cong_quot] with a
    constant dividend (m1 = 0) and non-constant divisor (m2 ≠ 0), the
    best abstraction depends on the GCD of quotients [|r1| div |c|] over
    divisor magnitudes [|c| ≤ |r1|] in γ(r2, m2). Computed by walking
    the two magnitude progressions of γ with an early exit at gcd = 1. *)

(** ** Helper lemmas about [quot_gcd_progression]. *)

(** Soundness: [quot_gcd_progression] divides [ar / (d + i·step)] for every
    valid index [i]. *)
Lemma quot_gcd_progression_div ar d step (i : nat) :
  1 <= d -> 1 <= step ->
  d + Z.of_nat i * step <= ar ->
  (quot_gcd_progression ar d step | ar / (d + Z.of_nat i * step)).
Proof.
  move=> Hd Hstep Hbound.
  have Hi_nn : 0 <= Z.of_nat i by lia.
  rewrite /quot_gcd_progression.
  case: (Z.ltb_spec ar d) => Har_d.
  - (* d > ar: contradicts Hbound. *) nia.
  - case: (Z.ltb_spec ar (d + step)) => Har_ds.
    + (* Single-element case: only i = 0 satisfies the bound. *)
      have Hi0 : Z.of_nat i = 0 by nia.
      have -> : d + Z.of_nat i * step = d by nia.
      exact: Z.divide_refl.
    + (* Multi-element case: result is 1, divides anything. *)
      exists (ar / (d + Z.of_nat i * step)). lia.
Qed.

(** Auxiliary: for [1 ≤ x ≤ n < 2·x], [n / x = 1]. *)
Lemma div_eq_one (n x : Z) : 1 <= x -> x <= n < 2 * x -> n / x = 1.
Proof.
  move=> Hx [Hxn Hn2x].
  symmetry. apply: (Z.div_unique_pos n x 1 (n - x)); lia.
Qed.

(** Optimality: any [m'] dividing every [ar / (d + i·step)] (for valid [i])
    divides [quot_gcd_progression ar d step]. *)
Lemma quot_gcd_progression_optimal ar d step (m' : Z) :
  1 <= d -> 1 <= step ->
  (forall i : nat, d + Z.of_nat i * step <= ar ->
     (m' | ar / (d + Z.of_nat i * step))) ->
  (m' | quot_gcd_progression ar d step).
Proof.
  move=> Hd Hstep Hall.
  rewrite /quot_gcd_progression.
  case: (Z.ltb_spec ar d) => Har_d; first exact: Z.divide_0_r.
  case: (Z.ltb_spec ar (d + step)) => Har_ds.
  - (* Single-element case: instantiate Hall at i = 0. *)
    have H0 := Hall 0%nat.
    have Heq : d + Z.of_nat 0 * step = d by simpl; lia.
    rewrite Heq in H0. apply: H0. lia.
  - (* Multi-element case: must show m' | 1. Find an i with quotient 1. *)
    suff: (m' | 1) by case=> q ->; exists q; lia.
    case: (Z_le_dec (2 * step) ar) => Hstep_small.
    + (* 2·step ≤ ar: take i_max = (ar - d) / step. *)
      pose imax := Z.to_nat ((ar - d) / step).
      have Himax_nn : 0 <= (ar - d) / step
        by apply: Z.div_pos; lia.
      have Himax_eq : Z.of_nat imax = (ar - d) / step
        by rewrite /imax Z2Nat.id.
      have Hquot : ar - d = (ar - d) / step * step + (ar - d) mod step
        by have := Z.div_mod (ar - d) step (ltac:(lia) : step <> 0); lia.
      have Hmod_bd : 0 <= (ar - d) mod step < step
        by apply: Z.mod_pos_bound; lia.
      have Hi_le : d + Z.of_nat imax * step <= ar by rewrite Himax_eq; lia.
      have Hi_gt : ar - step < d + Z.of_nat imax * step by rewrite Himax_eq; lia.
      have Hquot_one : ar / (d + Z.of_nat imax * step) = 1.
      { apply: div_eq_one; first lia. lia. }
      have := Hall imax Hi_le. rewrite Hquot_one. by [].
    + (* 2·step > ar: take i = 1. *)
      have H1eq : Z.of_nat 1 = 1 by [].
      have Hi_le : d + Z.of_nat 1 * step <= ar by rewrite H1eq; lia.
      have Hquot_one : ar / (d + Z.of_nat 1 * step) = 1.
      { apply: div_eq_one; first lia. rewrite H1eq. lia. }
      have := Hall 1%nat Hi_le. rewrite Hquot_one. by [].
Qed.

(** ** [quot_gcd_compute] correctness.

    Divisors of γ(r2, m2) with magnitude ≤ |r1| correspond to walks'
    indices. For rm = 0 (γ symmetric), one walk suffices. For rm > 0,
    two walks: positive magnitudes [rm + k·am] and negative magnitudes
    [(am − rm) + k·am]. *)

(** |Z.quot r1 c| = |r1| / |c|. *)
Lemma abs_quot r1 c : c <> 0 ->
  Z.abs (Z.quot r1 c) = Z.abs r1 / Z.abs c.
Proof.
  move=> Hc.
  have Hac : 0 < Z.abs c by case: (Z.abs_spec c); lia.
  rewrite (Z.quot_div _ _ Hc).
  have Hdnn : 0 <= Z.abs r1 / Z.abs c
    by apply: Z.div_pos; [apply: Z.abs_nonneg | exact Hac].
  rewrite !Z.abs_mul (Z.abs_eq _ Hdnn).
  have Hsgn_abs : forall x : Z, x <> 0 -> Z.abs (Z.sgn x) = 1.
  { move=> x Hx. case: (Z_lt_le_dec 0 x) => H.
    - by rewrite Z.sgn_pos.
    - rewrite Z.sgn_neg; lia. }
  case: (Z.eq_dec r1 0) => [->|Hr1].
  - by rewrite Z.sgn_0 Z.abs_0 Z.mul_0_l Z.mul_0_l Zdiv_0_l.
  - rewrite (Hsgn_abs _ Hr1) (Hsgn_abs _ Hc). lia.
Qed.

(** Any c ∈ γ(r, m) nonzero is of the form [c = q*|m| + rm] for some
    q ∈ ℤ, where [rm = r mod |m|] ∈ [0, |m|). *)
Lemma gamma_elem_form c r m :
  m <> 0 -> c ∈ γ[cong_ad] (r, m) ->
  exists q : Z, c = q * Z.abs m + r mod Z.abs m.
Proof.
  move=> Hm Hc.
  unfold_set in Hc. case: Hc => [j Hj].
  set am := Z.abs m.
  have Ham : 0 < am by case: (Z.abs_spec m); lia.
  set rm := r mod am.
  have Hr_eq : r = r / am * am + rm.
  { rewrite /rm. have := Z.div_mod r am (ltac:(lia) : am <> 0). lia. }
  exists (r / am + j * Z.sgn m).
  have Hm_abs := Z.abs_sgn m.
  rewrite /am. rewrite /am in Hr_eq. nia.
Qed.

(** [quot_gcd_compute] divides every [ar / |c|] for c ∈ γ(r2,m2), c ≠ 0,
    |c| ≤ ar (intermediate lemma). *)
Lemma quot_gcd_compute_div_ar_abs r1 r2 m2 c :
  m2 <> 0 -> c ∈ γ[cong_ad] (r2, m2) -> c <> 0 ->
  Z.abs c <= Z.abs r1 ->
  (quot_gcd_compute r1 r2 m2 | Z.abs r1 / Z.abs c).
Proof.
  move=> Hm2 Hc Hnz Hbound.
  set ar := Z.abs r1.
  set am := Z.abs m2.
  set rm := r2 mod am.
  have Ham : 0 < am by case: (Z.abs_spec m2); lia.
  have Hrm_bd : 0 <= rm < am by exact: Z.mod_pos_bound.
  have [q Hq] := gamma_elem_form c r2 m2 Hm2 Hc.
  have Hc_form : c = q * am + rm by rewrite Hq.
  have Hac_pos : 0 < Z.abs c by case: (Z.abs_spec c); lia.
  rewrite /quot_gcd_compute -/ar -/am -/rm.
  case: (Z.eqb_spec rm 0) => Hrm_zero.
  - (* rm = 0: |c| = |q|*am where q ≠ 0 (since c ≠ 0). *)
    have Habs_c : Z.abs c = Z.abs q * am.
    { rewrite Hc_form Hrm_zero Z.add_0_r Z.abs_mul.
      have -> : Z.abs am = am by apply: Z.abs_eq; lia. done. }
    have Hq_nn : 0 < Z.abs q by case: (Z.abs_spec q); lia.
    (* Pick index i such that am + i*am = |q|*am, i.e., i = |q| - 1. *)
    pose i := Z.to_nat (Z.abs q - 1).
    have Hi_eq : am + Z.of_nat i * am = Z.abs c.
    { rewrite Habs_c. rewrite /i Z2Nat.id; lia. }
    have Hi_le : am + Z.of_nat i * am <= ar by rewrite Hi_eq.
    have := quot_gcd_progression_div ar am am i (ltac:(lia) : 1 <= am)
      (ltac:(lia) : 1 <= am) Hi_le.
    rewrite Hi_eq. done.
  - (* rm ≠ 0: c is on pos-side (|c| = rm + k*am) or neg-side (|c| = (am-rm) + k*am). *)
    case: (Z_lt_le_dec 0 c) => Hc_sgn.
    + (* c > 0: c = q*am + rm, q ≥ 0, and c = rm + q*am. *)
      have Habs_c : Z.abs c = rm + q * am.
      { rewrite Hc_form. case: (Z.abs_spec c); lia. }
      have Hq_nn : 0 <= q by nia.
      pose i := Z.to_nat q.
      have Hi_eq : rm + Z.of_nat i * am = Z.abs c
        by rewrite Habs_c /i Z2Nat.id; lia.
      have Hi_le : rm + Z.of_nat i * am <= ar by rewrite Hi_eq.
      have Hpos := quot_gcd_progression_div ar rm am i
        (ltac:(lia) : 1 <= rm) (ltac:(lia) : 1 <= am) Hi_le.
      rewrite Hi_eq in Hpos.
      apply: Z.divide_trans; first exact: Z.gcd_divide_l. exact: Hpos.
    + (* c < 0: |c| = q' * am + (am - rm) for q' = -q - 1 ≥ 0. *)
      have Hc_lt : c < 0 by lia.
      have Hq_neg : q <= -1.
      { case: (Z_lt_le_dec q 0); last by nia. lia. }
      pose q' := -q - 1.
      have Hq'_nn : 0 <= q' by rewrite /q'; lia.
      have Habs_c : Z.abs c = (am - rm) + q' * am.
      { rewrite Hc_form. case: (Z.abs_spec c); nia. }
      pose i := Z.to_nat q'.
      have Hi_eq : (am - rm) + Z.of_nat i * am = Z.abs c
        by rewrite Habs_c /i Z2Nat.id; lia.
      have Hi_le : (am - rm) + Z.of_nat i * am <= ar by rewrite Hi_eq.
      have Hneg := quot_gcd_progression_div ar (am - rm) am i
        (ltac:(lia) : 1 <= am - rm) (ltac:(lia) : 1 <= am) Hi_le.
      rewrite Hi_eq in Hneg.
      apply: Z.divide_trans; first exact: Z.gcd_divide_r. exact: Hneg.
Qed.

(** Sound direction: [quot_gcd_compute] divides every [Z.quot r1 c]. *)
Lemma quot_gcd_compute_divides r1 r2 m2 c :
  m2 <> 0 -> c ∈ γ[cong_ad] (r2, m2) -> c <> 0 ->
  (quot_gcd_compute r1 r2 m2 | Z.quot r1 c).
Proof.
  move=> Hm2 Hc Hnz.
  apply/Z.divide_abs_r. rewrite abs_quot //.
  case: (Z_lt_le_dec (Z.abs r1) (Z.abs c)) => Hbound.
  - (* |c| > |r1|: ar / |c| = 0. *)
    have Hac_pos : 0 < Z.abs c by case: (Z.abs_spec c); lia.
    have -> : Z.abs r1 / Z.abs c = 0
      by apply: Z.div_small; split; [apply: Z.abs_nonneg | exact Hbound].
    exact: Z.divide_0_r.
  - exact: quot_gcd_compute_div_ar_abs.
Qed.

(** Optimality: any m' that divides every [Z.quot r1 c] divides
    [quot_gcd_compute r1 r2 m2]. *)
Lemma quot_gcd_compute_optimal r1 r2 m2 (m' : Z) :
  m2 <> 0 ->
  (forall c, c ∈ γ[cong_ad] (r2, m2) -> c <> 0 -> (m' | Z.quot r1 c)) ->
  (m' | quot_gcd_compute r1 r2 m2).
Proof.
  move=> Hm2 Hall.
  set ar := Z.abs r1.
  set am := Z.abs m2.
  set rm := r2 mod am.
  have Ham : 0 < am by case: (Z.abs_spec m2); lia.
  have Hrm_bd : 0 <= rm < am by exact: Z.mod_pos_bound.
  have Hsgn_mul : Z.sgn m2 * m2 = Z.abs m2 by have := Z.abs_sgn m2; nia.
  (* Convert: m' divides ar/|c| for each valid |c|. *)
  have Hdiv_abs : forall c, c ∈ γ[cong_ad] (r2, m2) -> c <> 0 ->
    (m' | Z.abs r1 / Z.abs c).
  { move=> c Hc Hnz. rewrite -abs_quot //. apply/Z.divide_abs_r. exact: Hall. }
  rewrite /quot_gcd_compute -/ar -/am -/rm.
  case: (Z.eqb_spec rm 0) => Hrm_zero.
  - (* rm = 0: elements of γ are (i+1)*am for i ≥ 0. *)
    apply: quot_gcd_progression_optimal; [lia | lia |].
    move=> i Hd.
    set d := am + Z.of_nat i * am.
    pose c := d.
    have Hr2_eq : r2 = r2 / am * am.
    { have := Z.div_mod r2 am (ltac:(lia) : am <> 0).
      fold rm. rewrite Hrm_zero. lia. }
    have Hc_in : c ∈ γ[cong_ad] (r2, m2).
    { unfold_set. rewrite /c /d.
      exists ((Z.of_nat i + 1 - r2 / am) * Z.sgn m2).
      have := Hsgn_mul. nia. }
    have Hc_ne : c <> 0.
    { rewrite /c /d. have := Z.of_nat i. nia. }
    have Habs : Z.abs c = d by rewrite /c /d; apply: Z.abs_eq; nia.
    have := Hdiv_abs c Hc_in Hc_ne. rewrite Habs. done.
  - (* rm ≠ 0: combine two progressions via Z.gcd_greatest. *)
    have Hr2_eq : r2 = r2 / am * am + rm.
    { have := Z.div_mod r2 am (ltac:(lia) : am <> 0). lia. }
    apply: Z.gcd_greatest.
    + (* Positive side: |c| = rm + i·am for c = rm + i·am > 0. *)
      apply: quot_gcd_progression_optimal; [lia | lia |].
      move=> i Hd. set d := rm + Z.of_nat i * am.
      pose c := d.
      have Hc_in : c ∈ γ[cong_ad] (r2, m2).
      { unfold_set. rewrite /c /d.
        exists ((Z.of_nat i - r2 / am) * Z.sgn m2).
        have := Hsgn_mul. nia. }
      have Hc_ne : c <> 0 by rewrite /c /d; nia.
      have Habs : Z.abs c = d by rewrite /c /d; apply: Z.abs_eq; nia.
      have := Hdiv_abs c Hc_in Hc_ne. rewrite Habs. done.
    + (* Negative side: |c| = (am - rm) + i·am for c = -(d) < 0. *)
      apply: quot_gcd_progression_optimal; [lia | lia |].
      move=> i Hd. set d := (am - rm) + Z.of_nat i * am.
      pose c := -d.
      have Hc_in : c ∈ γ[cong_ad] (r2, m2).
      { unfold_set. rewrite /c /d.
        exists ((-(Z.of_nat i + 1) - r2 / am) * Z.sgn m2).
        have := Hsgn_mul. nia. }
      have Hc_ne : c <> 0 by rewrite /c /d; nia.
      have Habs : Z.abs c = d.
      { rewrite /c Z.abs_opp. rewrite /d. apply: Z.abs_eq. nia. }
      have := Hdiv_abs c Hc_in Hc_ne. rewrite Habs. done.
Qed.

(** Identity used by [const_divides]: when [r2 ∣ m1] and ([m1 = 0] ∨ [r2 ∣ r1]),
    every dividend [r1 + k·m1] is a multiple of [r2], so [Z.quot] is exact. *)
Lemma cong_quot_const_divides_eq r1 m1 r2 k :
  r2 <> 0 ->
  (m1 = 0 \/ ((r2 | m1) /\ (r2 | r1))) ->
  Z.quot (r1 + k * m1) r2 = Z.quot r1 r2 + k * Z.quot m1 r2.
Proof.
  move=> Hr2 [Hm1 | [[qm Hqm] [qr Hqr]]].
  - subst m1. rewrite (Z.quot_0_l _ Hr2).
    have -> : r1 + k * 0 = r1 by ring.
    by rewrite Z.mul_0_r Z.add_0_r.
  - (* r1 = qr*r2, m1 = qm*r2 ⇒ r1 + k*m1 = (qr + k*qm)*r2 *)
    subst r1 m1.
    rewrite (Z.quot_mul _ _ Hr2) (Z.quot_mul _ _ Hr2).
    have -> : qr * r2 + k * (qm * r2) = (qr + k * qm) * r2 by ring.
    by rewrite (Z.quot_mul _ _ Hr2).
Qed.

Lemma cong_quot_sound:
  binary_overapproximation cong_ad cong_ad (WithBottom.ad cong_ad) cong_quot
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot).
Proof.
  move=> a2 a1 c0 [c2 [c1 [Hc2_in_a2 [Hc1_in_a1 [Hc1_ne Hc0]]]]].
  move: a2 a1 Hc2_in_a2 Hc1_in_a1 => [ra ma] [rb mb] Ha Hb.
  rewrite /cong_quot.
  have Htop (z : Z) : z ∈ γ[cong_ad] (0, 1).
  { unfold_set. apply Z.divide_1_l. }
  case Hmb: (mb =? 0); last first.
  { move: Hmb => /Z.eqb_neq Hmb.
    case Hma : (ma =? 0); last first.
    - simpl. move: Hc0 => <-. exact: Htop.
    - move/Z.eqb_eq: Hma => Hma.
      unfold_set in Ha. case: Ha => [k Hk].
      have Hc2 : c2 = ra by nia.
      simpl. move: Hc0 => <-. rewrite Hc2.
      unfold_set.
      have [j Hj] : (quot_gcd_compute ra rb mb | Z.quot ra c1)
        by apply: quot_gcd_compute_divides.
      by exists j; lia. }
  move: Hmb => /Z.eqb_eq Hmb.
  case Hrb: (rb =? 0).
  { move: Hrb => /Z.eqb_eq Hrb. subst rb mb.
    move/gamma_singleton in Hb.
    by rewrite Hb in Hc1_ne. }
  move: Hrb => /Z.eqb_neq Hrb.
  case Hcond : ((ma =? 0) || ((ma mod rb =? 0) && (ra mod rb =? 0))); last first.
  - simpl. move: Hc0 => <-. exact: Htop.
  - unfold_set in Ha. unfold_set in Hb. case: Ha => [k Hk]. case: Hb => [k' Hk'].
    have Hc1_eq : c1 = rb by nia.
    have Hc2 : c2 = ra + k * ma by nia.
    have Hdivs : ma = 0 \/ ((rb | ma) /\ (rb | ra)).
    { move: Hcond => /orP [/Z.eqb_eq ->|/andP [/Z.eqb_eq Hmam /Z.eqb_eq Hram]];
        [by left | right].
      split; by apply/Z.mod_divide. }
    simpl. move: Hc0 => <-. rewrite Hc2 Hc1_eq.
    rewrite (cong_quot_const_divides_eq _ _ _ _ Hrb Hdivs).
    unfold_set. by exists k; lia.
Qed.

(** ** Best-abstraction case lemmas for [cong_quot]. *)

Lemma cong_quot_best_divisor_zero (r1 m1 : Z) :
  BestAbstraction (A:=WithBottom.ad cong_ad) WithBottom.Bot
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (0, 0))).
Proof.
  apply: WithBottom.BestAbstraction_Bot.
  move=> c [c2 [c1 [_ [Hc1 [Hne _]]]]].
  unfold_set in Hc1. case: Hc1 => [k Hk].
  have : c1 = 0 by nia.
  by move/Hne.
Qed.

(** D1 analogue for quot: dividend = {0} forces every quotient to be 0. *)
Lemma cong_quot_exact_dividend_zero r2 m2 :
  m2 <> 0 ->
  ExactlyRepresents (A:=cong_ad) (0, 0)
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  (* Witness a nonzero element of γ(r2, m2). *)
  have [c1 [Hc1_in Hc1_ne]] : exists c, c ∈ γ[cong_ad] (r2, m2) /\ c <> 0.
  { case: (Z.eq_dec r2 0) => Hr2.
    - exists (r2 + m2). split; last by rewrite Hr2; lia.
      unfold_set. by exists 1; lia.
    - exists r2. split; last exact Hr2.
      unfold_set. by exists 0; lia. }
  split.
  - (* γ(0,0) ⊆ S: γ(0,0) = {0}; 0 ∈ S via (c2 := 0, c1 := c1, c1 ≠ 0). *)
    move=> c. move/gamma_singleton => ->.
    exists 0, c1. split; [by apply/gamma_singleton|].
    split; [exact Hc1_in|]. split; [exact Hc1_ne|].
    by rewrite (Z.quot_0_l _ Hc1_ne).
  - (* S ⊆ γ(0,0): every element is 0. *)
    move=> c [c2 [c1' [Ha [_ [Hne Hd]]]]].
    move/gamma_singleton in Ha.
    rewrite Ha (Z.quot_0_l _ Hne) in Hd. subst c.
    by apply/gamma_singleton.
Qed.

Lemma cong_quot_best_dividend_zero r2 m2 :
  m2 <> 0 ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 0))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  have [c1 [Hc1_in Hc1_ne]] : exists c, c ∈ γ[cong_ad] (r2, m2) /\ c <> 0.
  { case: (Z.eq_dec r2 0) => Hr2.
    - exists (r2 + m2). split; last by rewrite Hr2; lia.
      unfold_set. by exists 1; lia.
    - exists r2. split; last exact Hr2.
      unfold_set. by exists 0; lia. }
  apply: WithBottom.BestAbstraction_NotBot.
  - (* non-empty S witness *)
    exists 0, 0, c1. split; [by exists 0; lia|].
    split; [exact Hc1_in|]. split; [exact Hc1_ne|].
    exact: Z.quot_0_l.
  - apply: is_alpha_is_best_abstraction.
    apply: exact_is_is_alpha. exact: cong_quot_exact_dividend_zero.
Qed.

(** const_divides exact case: [r2 | m1 ∧ (m1 = 0 ∨ r2 | r1)]. *)
Lemma cong_quot_exact_const_divides r1 m1 r2 :
  r2 <> 0 ->
  (m1 = 0 \/ ((r2 | m1) /\ (r2 | r1))) ->
  ExactlyRepresents (A:=cong_ad) (Z.quot r1 r2, Z.quot m1 r2)
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hdivs.
  split.
  - (* γ(Z.quot r1 r2, Z.quot m1 r2) ⊆ S *)
    move=> c Hc. unfold_set in Hc. case: Hc => [k Hk].
    exists (r1 + k * m1), r2.
    split; [by exists k; lia|].
    split; [by exists 0; lia|]. split; first exact Hr2.
    rewrite (cong_quot_const_divides_eq _ _ _ _ Hr2 Hdivs). lia.
  - (* S ⊆ γ *)
    move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]].
    unfold_set in Ha. move/gamma_singleton in Hb.
    case: Ha => [k Hk].
    have Hc2_eq : c2 = r1 + k * m1 by lia.
    subst c. rewrite Hc2_eq Hb.
    rewrite (cong_quot_const_divides_eq _ _ _ _ Hr2 Hdivs).
    unfold_set. by exists k; lia.
Qed.

Lemma cong_quot_best_const_divides r1 m1 r2 :
  r2 <> 0 ->
  (m1 = 0 \/ ((r2 | m1) /\ (r2 | r1))) ->
  BestAbstraction (A:=WithBottom.ad cong_ad)
    (WithBottom.NotBot (Z.quot r1 r2, Z.quot m1 r2))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hdivs.
  apply: WithBottom.BestAbstraction_NotBot.
  - (* witness: Z.quot r1 r2 ∈ S via (c2 := r1, c1 := r2 ≠ 0) *)
    exists (Z.quot r1 r2), r1, r2. split; [by exists 0; lia|].
    split; [by exists 0; lia|]. split; [exact Hr2 | reflexivity].
  - apply: is_alpha_is_best_abstraction.
    apply: exact_is_is_alpha. exact: cong_quot_exact_const_divides.
Qed.

(** [const_pos_nondivides] for quot, [m1 > 0] only.

    The carry argument [carry_witnesses_divides_one] wants witnesses
    for [k ∈ [0, r2]] with [Z.div] computations. Z.quot agrees with
    Z.div on nonneg dividends, so we shift the witness range by
    [K := |r1|]: with [m1 ≥ 1], [r1 + K·m1 ≥ 0] regardless of r1's
    sign, and the shifted base [r1' := r1 + K·m1] satisfies the nonneg
    condition. Since [γ(r1', m1) = γ(r1, m1)] (same congruence class),
    the witnesses come from the original set. *)
Lemma cong_quot_best_const_pos_m1_pos r1 m1 r2 :
  0 < r2 -> 0 < m1 -> ~(r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hm1 Hnd.
  have Hr2_ne : r2 <> 0 by lia.
  apply: WithBottom.BestAbstraction_NotBot.
  - (* non-emptiness: Z.quot r1 r2 ∈ S *)
    exists (Z.quot r1 r2), r1, r2. split; [by exists 0; lia|].
    split; [by exists 0; lia|]. split; [exact Hr2_ne | reflexivity].
  - split.
    + move=> c _. unfold_set. exact: Z.divide_1_l.
    + move=> [r' m'] HS.
      pose K := Z.abs r1.
      pose r1' := r1 + K * m1.
      have Habs : - Z.abs r1 <= r1 by case: (Z.abs_spec r1); lia.
      have Hr1'_nn : 0 <= r1'.
      { rewrite /r1' /K. nia. }
      (* V_in with shifted base: every k ∈ [0, r2] gives nonneg dividend. *)
      have V_in : forall k, 0 <= k <= r2 -> (m' | (r1' + k*m1) / r2 - r').
      { move=> k Hk.
        have Hnonneg : 0 <= r1' + k*m1 by rewrite /r1' /K; nia.
        have Hmem : Z.quot (r1' + k*m1) r2 ∈ γ[cong_ad] (r', m').
        { apply: HS. exists (r1' + k*m1), r2.
          split.
          - (* r1' + k*m1 = r1 + (K+k)*m1 ∈ γ(r1, m1) *)
            exists (K + k). rewrite /r1'. lia.
          - split; [by exists 0; lia|].
            split; [exact Hr2_ne | reflexivity]. }
        unfold_set in Hmem.
        by rewrite (Z.quot_div_nonneg _ _ Hnonneg Hr2) in Hmem. }
      have Hone := carry_witnesses_divides_one _ _ _ _ _ Hr2 Hnd V_in.
      split; first exact: Hone.
      apply: Z.divide_trans Hone _. exact: Z.divide_1_l.
Qed.

(** γ(r, m) = γ(r, -m): the congruence class is sign-insensitive in the step. *)
Local Lemma cong_gamma_sym_m r m :
  γ[cong_ad] (r, m) ⊆⊇ γ[cong_ad] (r, -m).
Proof.
  split; move=> c; unfold_set => [[k Hk]]; unfold_set;
    exists (-k); lia.
Qed.

(** Transport of [collecting_binary_forward_partial] along γ-equivalence
    in the dividend set, for any fixed divisor set. *)
Local Lemma collecting_quot_gamma_cong_l r1 m1 m1' (S1 : propset Z) :
  γ[cong_ad] (r1, m1) ⊆⊇ γ[cong_ad] (r1, m1') ->
  collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
    (γ[cong_ad] (r1, m1)) S1
  ⊆⊇
  collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
    (γ[cong_ad] (r1, m1')) S1.
Proof.
  move=> [Hsub1 Hsub2]. split.
  - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]]. exists c2, c1.
    split; [exact: Hsub1 | split; done].
  - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]]. exists c2, c1.
    split; [exact: Hsub2 | split; done].
Qed.

(** Full positive-divisor case: any m1 ≠ 0. Reduces [m1 < 0] to [m1 > 0]
    via γ(r1, m1) = γ(r1, -m1). *)
Lemma cong_quot_best_const_pos r1 m1 r2 :
  0 < r2 -> ~(r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  have Hm1_ne : m1 <> 0.
  { move=> H. apply: Hnd. by exists 0; lia. }
  case: (Z_lt_le_dec 0 m1) => Hm1_sgn.
  - exact: cong_quot_best_const_pos_m1_pos.
  - have Hmm1 : 0 < -m1 by lia.
    have Hnd' : ~(r2 | -m1).
    { move=> [k Hk]. apply: Hnd. by exists (-k); lia. }
    apply: best_abstraction_equiv;
      last (symmetry; apply: collecting_quot_gamma_cong_l; exact: cong_gamma_sym_m).
    exact: cong_quot_best_const_pos_m1_pos _ _ _ Hr2 Hmm1 Hnd'.
Qed.

(** Sign-correction: for [c < 0] with [r ∤ c], [Z.quot c r = Z.div c r + 1].
    (For [c ≥ 0] or [r ∣ c], Z.quot and Z.div agree.) *)
Lemma Z_quot_neg_nondivides c r :
  0 < r -> c < 0 -> ~(r | c) ->
  Z.quot c r = Z.div c r + 1.
Proof.
  move=> Hr Hc Hnd.
  have Hr_ne : r <> 0 by lia.
  have Hmod_nc : (-c) mod r <> 0.
  { move=> Heq. apply: Hnd.
    have [k Hk] : (r | -c) by apply/Z.mod_divide.
    by exists (-k); lia. }
  have Hnc_nn : 0 <= -c by lia.
  have Hqc : Z.quot c r = -(Z.div (-c) r).
  { have Hc_eq : c = -(-c) by ring.
    rewrite {1}Hc_eq (Z.quot_opp_l _ _ Hr_ne).
    by rewrite (Z.quot_div_nonneg _ _ Hnc_nn Hr). }
  have Hdc : Z.div c r = -(Z.div (-c) r) - 1.
  { have := Z.div_opp_l_nz (-c) r Hr_ne Hmod_nc.
    by rewrite Z.opp_involutive => ->. }
  lia.
Qed.

(** [const_divides_ndr1] sub-case: [r2 > 0 ∧ m1 > 0 ∧ r2 ∣ m1 ∧ r2 ∤ r1].
    The quot set contains both a "regular" gap of q (between two
    positive-dividend witnesses) and a reduced gap of q − 1 (at the
    sign-transition between c1 ≥ 0 and c1 < 0). Hence m' ∣ q and
    m' ∣ q − 1, forcing m' ∣ 1. *)
Lemma cong_quot_best_const_divides_ndr1_m1_pos r1 m1 r2 :
  0 < r2 -> 0 < m1 -> (r2 | m1) -> ~(r2 | r1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hm1 Hr2_divs_m1 Hnd.
  have Hr2_ne : r2 <> 0 by lia.
  have Hm1_ne : m1 <> 0 by lia.
  case: Hr2_divs_m1 => q_ Hq_eq.
  have Hq_pos : 0 < q_ by nia.
  apply: WithBottom.BestAbstraction_NotBot.
  - exists (Z.quot r1 r2), r1, r2. split; [by exists 0; lia|].
    split; [by exists 0; lia|]. split; [exact Hr2_ne | reflexivity].
  - split.
    + move=> c _. unfold_set. exact: Z.divide_1_l.
    + move=> [r' m'] HS.
      (* Choose k_a such that c1_a := r1 + k_a*m1 ∈ [0, m1). *)
      pose k_a := -(r1 / m1).
      pose c1_a := r1 + k_a * m1.
      pose c1_b := c1_a - m1.    (* in [-m1, 0), same residue mod m1, so same mod r2 *)
      pose c1_c := c1_a + m1.    (* in [m1, 2m1), nonneg *)
      have Hc1a_range : 0 <= c1_a < m1.
      { rewrite /c1_a /k_a.
        have := Z.mod_pos_bound r1 m1 Hm1.
        have := Z.div_mod r1 m1 Hm1_ne. lia. }
      have Hc1b_range : -m1 <= c1_b < 0 by rewrite /c1_b; lia.
      have Hc1c_range : m1 <= c1_c < 2*m1 by rewrite /c1_c; lia.
      (* Membership in γ(r1, m1) *)
      have Ha_in : c1_a ∈ γ[cong_ad] (r1, m1) by unfold_set; exists k_a; lia.
      have Hb_in : c1_b ∈ γ[cong_ad] (r1, m1).
      { unfold_set. exists (k_a - 1). rewrite /c1_b /c1_a. lia. }
      have Hc_in : c1_c ∈ γ[cong_ad] (r1, m1).
      { unfold_set. exists (k_a + 1). rewrite /c1_c /c1_a. lia. }
      (* r2 ∤ c1_b (same residue mod r2 as r1, which r2 ∤) *)
      have Hb_nd : ~(r2 | c1_b).
      { move=> [l Hl]. apply: Hnd.
        have Hc1b_expr : c1_b = r1 + (k_a - 1) * (q_ * r2)
          by rewrite /c1_b /c1_a; rewrite -Hq_eq; ring.
        exists (l - (k_a - 1) * q_). nia. }
      (* Z.quot values *)
      have Hqa_div : Z.quot c1_a r2 = Z.div c1_a r2
        by apply: Z.quot_div_nonneg; lia.
      have Hqc_div : Z.quot c1_c r2 = Z.div c1_c r2
        by apply: Z.quot_div_nonneg; lia.
      have Hqb_div : Z.quot c1_b r2 = Z.div c1_b r2 + 1.
      { apply: Z_quot_neg_nondivides => //; lia. }
      (* Z.div values: linear via Z.div_add *)
      have Hdiv_add : forall (c : Z) (k : Z),
          c = c1_a + k * m1 -> Z.div c r2 = Z.div c1_a r2 + k * q_.
      { move=> c k ->.
        have -> : c1_a + k * m1 = c1_a + (k * q_) * r2 by nia.
        by rewrite (Z.div_add _ _ _ Hr2_ne). }
      have Hda_b : Z.div c1_b r2 = Z.div c1_a r2 - q_.
      { have : Z.div c1_b r2 = Z.div c1_a r2 + (-1) * q_.
        { apply: Hdiv_add. rewrite /c1_b. ring. }
        lia. }
      have Hda_c : Z.div c1_c r2 = Z.div c1_a r2 + q_.
      { have : Z.div c1_c r2 = Z.div c1_a r2 + 1 * q_.
        { apply: Hdiv_add. rewrite /c1_c. ring. }
        lia. }
      (* Feed HS *)
      have Hma_in : Z.quot c1_a r2 ∈ γ[cong_ad] (r', m').
      { apply: HS. exists c1_a, r2. split; [exact Ha_in|].
        split; [by exists 0; lia|]. split; [exact Hr2_ne | reflexivity]. }
      have Hmb_in : Z.quot c1_b r2 ∈ γ[cong_ad] (r', m').
      { apply: HS. exists c1_b, r2. split; [exact Hb_in|].
        split; [by exists 0; lia|]. split; [exact Hr2_ne | reflexivity]. }
      have Hmc_in : Z.quot c1_c r2 ∈ γ[cong_ad] (r', m').
      { apply: HS. exists c1_c, r2. split; [exact Hc_in|].
        split; [by exists 0; lia|]. split; [exact Hr2_ne | reflexivity]. }
      unfold_set in Hma_in. unfold_set in Hmb_in. unfold_set in Hmc_in.
      set x := Z.div c1_a r2.
      (* m' | (Z.quot c1_a - r') - (Z.quot c1_b - r') = Z.quot c1_a - Z.quot c1_b *)
      have Hqab : (m' | q_ - 1).
      { have H := Z.divide_sub_r _ _ _ Hma_in Hmb_in.
        have Heq : (Z.quot c1_a r2 - r') - (Z.quot c1_b r2 - r') = q_ - 1.
        { rewrite Hqa_div Hqb_div Hda_b /x. lia. }
        by rewrite Heq in H. }
      have Hqca : (m' | q_).
      { have H := Z.divide_sub_r _ _ _ Hmc_in Hma_in.
        have Heq : (Z.quot c1_c r2 - r') - (Z.quot c1_a r2 - r') = q_.
        { rewrite Hqa_div Hqc_div Hda_c /x. lia. }
        by rewrite Heq in H. }
      have Hone : (m' | 1).
      { have H := Z.divide_sub_r _ _ _ Hqca Hqab.
        by have -> : 1 = q_ - (q_ - 1) by lia. }
      split; first exact: Hone.
      apply: Z.divide_trans Hone _. exact: Z.divide_1_l.
Qed.

(** Any sign of [m1], for [0 < r2] and [r2 ∣ m1, r2 ∤ r1]. *)
Lemma cong_quot_best_const_divides_ndr1_pos r1 m1 r2 :
  0 < r2 -> m1 <> 0 -> (r2 | m1) -> ~(r2 | r1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hm1 Hdiv Hnd.
  case: (Z_lt_le_dec 0 m1) => Hm1_sgn.
  - exact: cong_quot_best_const_divides_ndr1_m1_pos.
  - have Hmm1 : 0 < -m1 by lia.
    have Hdiv' : (r2 | -m1) by case: Hdiv => [q ->]; exists (-q); lia.
    apply: best_abstraction_equiv;
      last (symmetry; apply: collecting_quot_gamma_cong_l; exact: cong_gamma_sym_m).
    exact: cong_quot_best_const_divides_ndr1_m1_pos _ _ _ Hr2 Hmm1 Hdiv' Hnd.
Qed.

(** [r2 < 0] sub-case, by reduction to positive [r2] via [Z.quot_opp_opp]
    and the [c1 ↔ -c1] bijection on γ. *)
Lemma cong_quot_best_const_divides_ndr1_neg r1 m1 r2 :
  r2 < 0 -> m1 <> 0 -> (r2 | m1) -> ~(r2 | r1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hm1 Hdiv Hnd.
  have Hr2_ne : r2 <> 0 by lia.
  have Hr2' : 0 < -r2 by lia.
  have Hdiv' : (-r2 | m1) by case: Hdiv => [k Hk]; exists (-k); lia.
  have Hnd' : ~(-r2 | -r1).
  { move=> [k Hk]. apply: Hnd. by exists k; lia. }
  have Hset :
    collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
      (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))
    ⊆⊇
    collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
      (γ[cong_ad] (-r1, m1)) (γ[cong_ad] (-r2, 0)).
  { split.
    - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]].
      exists (-c2), (-c1).
      split; [|split; [|split]].
      + unfold_set. unfold_set in Ha. case: Ha => [k Hk].
        exists (-k). lia.
      + unfold_set. unfold_set in Hb. case: Hb => [k Hk].
        exists 0. nia.
      + lia.
      + by rewrite (Z.quot_opp_opp _ _ Hne).
    - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]].
      exists (-c2), (-c1).
      split; [|split; [|split]].
      + unfold_set. unfold_set in Ha. case: Ha => [k Hk].
        exists (-k). lia.
      + unfold_set. unfold_set in Hb. case: Hb => [k Hk].
        exists 0. nia.
      + lia.
      + have Hne' : -c1 <> 0 by lia.
        rewrite -(Z.quot_opp_opp (-c2) (-c1) Hne').
        by rewrite !Z.opp_involutive. }
  apply: best_abstraction_equiv; last by symmetry; exact: Hset.
  exact: cong_quot_best_const_divides_ndr1_pos _ _ _ Hr2' Hm1 Hdiv' Hnd'.
Qed.

(** nonconstant_divisor for quot, [m1 > 0] sub-case.

    Strategy: pick a large positive c2 ∈ γ(r2,m2) with [c2 ≥ m1 + 2].
    Then find c1_a ∈ γ(r1,m1) ∩ [c2, 2c2) and c1_b ∈ γ(r1,m1) ∩ [0, m1).
    Both intervals have length ≥ m1 so γ-membership is guaranteed;
    [Z.quot c1_a c2 = 1] (nonneg, in [c2, 2c2)), [Z.quot c1_b c2 = 0]
    (nonneg, in [0, c2)). So {0, 1} ⊆ partial quot set and m' ∣ 1. *)
Lemma cong_quot_best_nonconstant_divisor_m1_pos r1 m1 r2 m2 :
  m2 <> 0 -> 0 < m1 ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2 Hm1.
  have Hm1_ne : m1 <> 0 by lia.
  have Hm2_abs : 1 <= Z.abs m2.
  { have := Z.abs_nonneg m2. case: (Z.abs_spec m2); lia. }
  have Hsgn_mul : Z.sgn m2 * m2 = Z.abs m2.
  { have := Z.abs_sgn m2. nia. }
  pose A := Z.abs r2 + m1 + 2.
  have HA : m1 + 2 <= A.
  { rewrite /A. have := Z.abs_nonneg r2. lia. }
  pose c2 := r2 + A * Z.sgn m2 * m2.
  have Hr2_abs : - Z.abs r2 <= r2 by case: (Z.abs_spec r2); lia.
  have Hc2_eq : c2 = r2 + A * Z.abs m2.
  { rewrite /c2. have := Hsgn_mul. nia. }
  have Hc2_bounds : m1 + 2 <= c2 by rewrite Hc2_eq /A; nia.
  have Hc2_pos : 0 < c2 by lia.
  have Hc2_in : c2 ∈ γ[cong_ad] (r2, m2)
    by unfold_set; exists (A * Z.sgn m2); rewrite /c2; ring.
  have Hc2_ne : c2 <> 0 by lia.
  (* c1_b := r1 mod m1, nonneg and < m1 ≤ c2. *)
  pose k_b := -(r1 / m1).
  pose c1_b := r1 + k_b * m1.
  have Hc1b_eq : c1_b = r1 mod m1.
  { rewrite /c1_b /k_b.
    have := Z.div_mod r1 m1 Hm1_ne. lia. }
  have Hc1b_bounds : 0 <= c1_b < m1
    by rewrite Hc1b_eq; exact: Z.mod_pos_bound.
  have Hc1b_in : c1_b ∈ γ[cong_ad] (r1, m1)
    by unfold_set; exists k_b; rewrite /c1_b; lia.
  (* c1_a := r1 + k_a*m1 with c2 ≤ c1_a < c2 + m1 < 2*c2. *)
  pose k_a := (c2 - r1 + m1 - 1) / m1.
  pose c1_a := r1 + k_a * m1.
  have Hc1a_bounds : c2 <= c1_a < c2 + m1.
  { rewrite /c1_a /k_a.
    have := Z.div_mod (c2 - r1 + m1 - 1) m1 Hm1_ne.
    have := Z.mod_pos_bound (c2 - r1 + m1 - 1) m1 Hm1. nia. }
  have Hc1a_ubound : c1_a < 2 * c2 by lia.
  have Hc1a_pos : 0 < c1_a by lia.
  have Hc1a_in : c1_a ∈ γ[cong_ad] (r1, m1)
    by unfold_set; exists k_a; rewrite /c1_a; lia.
  apply: WithBottom.BestAbstraction_NotBot.
  - (* Non-empty: 0 ∈ partial set via Z.quot c1_b c2 = 0. *)
    exists 0, c1_b, c2. split; [exact Hc1b_in|].
    split; [exact Hc2_in|]. split; [exact Hc2_ne|].
    rewrite (Z.quot_div_nonneg _ _ (ltac:(lia) : 0 <= c1_b) Hc2_pos).
    apply: Z.div_small. lia.
  - split.
    + move=> c _. unfold_set. exact: Z.divide_1_l.
    + move=> [r' m'] HS.
      have H0_in : 0 ∈ collecting_binary_forward_partial
                         (fun _ c1 => c1 <> 0) Z.quot
                         (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)).
      { exists c1_b, c2.
        split; [exact Hc1b_in|].
        split; [exact Hc2_in|]. split; [exact Hc2_ne|].
        rewrite (Z.quot_div_nonneg _ _ (ltac:(lia) : 0 <= c1_b) Hc2_pos).
        apply: Z.div_small. lia. }
      have H1_in : 1 ∈ collecting_binary_forward_partial
                         (fun _ c1 => c1 <> 0) Z.quot
                         (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)).
      { exists c1_a, c2.
        split; [exact Hc1a_in|].
        split; [exact Hc2_in|]. split; [exact Hc2_ne|].
        rewrite (Z.quot_div_nonneg _ _ (ltac:(lia) : 0 <= c1_a) Hc2_pos).
        symmetry. apply: (Z.div_unique _ _ 1 (c1_a - c2)); lia. }
      have := HS _ H0_in. unfold_set => H0'.
      have := HS _ H1_in. unfold_set => H1'.
      have Hone : (m' | 1).
      { have H := Z.divide_sub_r _ _ _ H1' H0'.
        by have -> : 1 = (1 - r') - (0 - r') by ring. }
      split; first exact: Hone.
      exact: H0'.
Qed.

(** Any sign of m1 (nonzero): reduce m1 < 0 to m1 > 0 via γ-symmetry. *)
Lemma cong_quot_best_nonconstant_divisor_m1_nz (r1 m1 r2 m2 : Z) :
  m2 <> 0 -> m1 <> 0 ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2 Hm1.
  case: (Z_lt_le_dec 0 m1) => Hm1_sgn.
  - exact: cong_quot_best_nonconstant_divisor_m1_pos.
  - have Hmm1 : 0 < -m1 by lia.
    apply: best_abstraction_equiv;
      last (symmetry; apply: collecting_quot_gamma_cong_l; exact: cong_gamma_sym_m).
    exact: cong_quot_best_nonconstant_divisor_m1_pos _ _ _ _ Hm2 Hmm1.
Qed.

(** 0 is always in the partial quot set when m1 = 0 and m2 ≠ 0:
    pick any nonzero c2 ∈ γ(r2, m2) of magnitude greater than |r1|, and
    Z.quot r1 c2 = 0. *)
Lemma zero_in_quot_set_m1_zero r1 r2 m2 :
  m2 <> 0 ->
  0 ∈ collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
        (γ[cong_ad] (r1, 0)) (γ[cong_ad] (r2, m2)).
Proof.
  move=> Hm2.
  have Hm2_abs : 1 <= Z.abs m2.
  { have := Z.abs_nonneg m2. case: (Z.abs_spec m2); lia. }
  have Hsgn_mul : Z.sgn m2 * m2 = Z.abs m2 by have := Z.abs_sgn m2; nia.
  pose A := Z.abs r1 + Z.abs r2 + 1.
  pose c2 := r2 + A * Z.sgn m2 * m2.
  have HA : 1 <= A.
  { rewrite /A. have := Z.abs_nonneg r1. have := Z.abs_nonneg r2. lia. }
  have Hr2_abs : - Z.abs r2 <= r2 by case: (Z.abs_spec r2); lia.
  have Hc2_eq : c2 = r2 + A * Z.abs m2 by rewrite /c2; nia.
  have Hc2_bounds : Z.abs r1 + 1 <= c2 by rewrite Hc2_eq /A; nia.
  have Hr1_abs : Z.abs r1 >= 0 by have := Z.abs_nonneg r1; lia.
  have Hc1_abs : - Z.abs r1 <= r1 <= Z.abs r1 by case: (Z.abs_spec r1); lia.
  have Hc2_pos : 0 < c2 by lia.
  have Hc2_ne : c2 <> 0 by lia.
  have Hc2_in : c2 ∈ γ[cong_ad] (r2, m2)
    by unfold_set; exists (A * Z.sgn m2); rewrite /c2; ring.
  exists r1, c2. split; [by exists 0; lia|].
  split; [exact Hc2_in|]. split; [exact Hc2_ne|].
  apply/Z.quot_small_iff => //.
  have -> : Z.abs c2 = c2 by case: (Z.abs_spec c2); lia.
  case: (Z.abs_spec r1); lia.
Qed.

(** Best abstraction for the m1 = 0 case (any r1), using the refined
    [cong_quot] result [(0, quot_gcd_compute r1 r2 m2)]. *)
Lemma cong_quot_best_m1_zero r1 r2 m2 :
  m2 <> 0 ->
  BestAbstraction (A:=WithBottom.ad cong_ad)
    (WithBottom.NotBot (0, quot_gcd_compute r1 r2 m2))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  set m := quot_gcd_compute r1 r2 m2.
  split.
  - (* Overapproximates *)
    move=> c0 [c1 [c2 [Hc1 [Hc2 [Hne Hd]]]]].
    unfold_set in Hc1. case: Hc1 => [k Hk].
    have Hc1_eq : c1 = r1 by nia.
    subst c0. unfold_set.
    have [j Hj] : (m | Z.quot c1 c2).
    { rewrite Hc1_eq. apply: quot_gcd_compute_divides => //. }
    by exists j; lia.
  - move=> [|[r' m']] Ha'.
    + (* a' = Bot: contradicted by 0 ∈ S *)
      exfalso. have H0 := zero_in_quot_set_m1_zero r1 r2 m2 Hm2.
      have := Ha' _ H0. by rewrite propset_elem_of_iff.
    + simpl. split.
      * (* m' | m *)
        have H0 := zero_in_quot_set_m1_zero r1 r2 m2 Hm2.
        have := Ha' _ H0. unfold_set => [[j Hj]].
        (* Hj : 0 - r' = j * m'. So m' | r'. *)
        have Hmr' : (m' | r') by exists (-j); lia.
        apply: quot_gcd_compute_optimal => //.
        move=> c Hc_in Hc_nz.
        have Hin : Z.quot r1 c ∈
          collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
            (γ[cong_ad] (r1, 0)) (γ[cong_ad] (r2, m2)).
        { exists r1, c. split; [by exists 0; lia|].
          split; [exact Hc_in|]. split; [exact Hc_nz | reflexivity]. }
        have := Ha' _ Hin. unfold_set => [[j2 Hj2]].
        case: Hmr' => [l Hl].
        exists (j2 + l). lia.
      * (* m' | 0 - r' = -r' *)
        have H0 := zero_in_quot_set_m1_zero r1 r2 m2 Hm2.
        have := Ha' _ H0. by unfold_set => [[j Hj]]; exists j; lia.
Qed.

Lemma cong_quot_best_const_neg r1 m1 r2 :
  r2 < 0 -> ~(r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  have Hr2_ne : r2 <> 0 by lia.
  have Hr2' : 0 < -r2 by lia.
  have Hnd' : ~(-r2 | m1).
  { move=> [k Hk]. apply: Hnd. by exists (-k); lia. }
  (* Build set equivalence: divisor r2 ↔ dividend-flip to -r2. *)
  have Hset :
    collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
      (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))
    ⊆⊇
    collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
      (γ[cong_ad] (-r1, m1)) (γ[cong_ad] (-r2, 0)).
  { split.
    - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]].
      exists (-c2), (-c1).
      split; [|split; [|split]].
      + unfold_set. unfold_set in Ha. case: Ha => [k Hk].
        exists (-k). lia.
      + unfold_set. unfold_set in Hb. case: Hb => [k Hk].
        exists 0. nia.
      + lia.
      + by rewrite (Z.quot_opp_opp _ _ Hne).
    - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]].
      exists (-c2), (-c1).
      split; [|split; [|split]].
      + unfold_set. unfold_set in Ha. case: Ha => [k Hk].
        exists (-k). lia.
      + unfold_set. unfold_set in Hb. case: Hb => [k Hk].
        exists 0. nia.
      + lia.
      + have Hne' : -c1 <> 0 by lia.
        rewrite -(Z.quot_opp_opp (-c2) (-c1) Hne').
        by rewrite !Z.opp_involutive. }
  apply: best_abstraction_equiv; last by symmetry; exact: Hset.
  exact: cong_quot_best_const_pos _ _ _ Hr2' Hnd'.
Qed.

(** Aggregate: [cong_quot] is a best abstraction for [Z.quot] under
    partial semantics (divisor ≠ 0). Dispatches on the [if]-structure of
    [cong_quot]:
    - divisor_zero (r2 = m2 = 0) → Bot
    - const_divides (m2 = 0, r2 ≠ 0, m1 = 0 ∨ (r2|m1 ∧ r2|r1)) → exact
    - const_pos/neg (m2 = 0, r2 ≠ 0, r2 ∤ m1) → top
    - const_divides_ndr1_pos/neg (m2 = 0, r2 ≠ 0, r2|m1 ∧ r2∤r1 ∧ m1≠0) → top
    - dividend_zero (m2 ≠ 0, r1 = m1 = 0) → exact
    - nonconstant_divisor (m2 ≠ 0, otherwise) → top (stub) *)
Lemma cong_quot_best :
  binary_best cong_ad cong_ad (WithBottom.ad cong_ad) cong_quot
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot).
Proof.
  move=> a2 a1.
  move: a2 a1 => [r1 m1] [r2 m2].
  rewrite /cong_quot.
  case Hm2 : (m2 =? 0).
  - move/Z.eqb_eq: Hm2 => ->.
    case Hr2 : (r2 =? 0).
    + move/Z.eqb_eq: Hr2 => ->. exact: cong_quot_best_divisor_zero.
    + move/Z.eqb_neq: Hr2 => Hr2.
      case Hcond : ((m1 =? 0) || ((m1 mod r2 =? 0) && (r1 mod r2 =? 0))).
      * (* const_divides *)
        apply: cong_quot_best_const_divides => //.
        move: Hcond => /orP [/Z.eqb_eq ->|/andP [/Z.eqb_eq Hmm /Z.eqb_eq Hrm]].
        -- by left.
        -- right. split; by apply/Z.mod_divide.
      * (* top: extract m1 ≠ 0 and NOT(r2|m1 ∧ r2|r1). *)
        have Hm1 : m1 <> 0.
        { move=> H. move: Hcond. by rewrite H /=. }
        have Hcond2 : ~((r2 | m1) /\ (r2 | r1)).
        { move=> [Hd1 Hd2]. move: Hcond.
          have Hb1 : m1 mod r2 = 0 by apply/Z.mod_divide.
          have Hb2 : r1 mod r2 = 0 by apply/Z.mod_divide.
          by rewrite Hb1 Hb2 /= orb_true_r. }
        case Hdiv_m1 : (m1 mod r2 =? 0); last first.
        -- (* r2 ∤ m1: const_pos or const_neg *)
           move/Z.eqb_neq: Hdiv_m1 => Hmm.
           have Hnd : ~(r2 | m1).
           { move=> H. apply: Hmm. by apply/Z.mod_divide. }
           case: (Z_lt_le_dec 0 r2) => Hr2sgn.
           ++ exact: cong_quot_best_const_pos.
           ++ have Hr2lt : r2 < 0 by lia.
              exact: cong_quot_best_const_neg.
        -- (* r2 | m1 ∧ r2 ∤ r1 (must hold since const_divides failed): const_divides_ndr1 *)
           move/Z.eqb_eq: Hdiv_m1 => Hmm.
           have Hdiv_m1' : (r2 | m1) by apply/Z.mod_divide.
           have Hdiv_r1 : ~(r2 | r1).
           { move=> H. exact: Hcond2 (conj Hdiv_m1' H). }
           case: (Z_lt_le_dec 0 r2) => Hr2sgn.
           ++ exact: cong_quot_best_const_divides_ndr1_pos.
           ++ have Hr2lt : r2 < 0 by lia.
              exact: cong_quot_best_const_divides_ndr1_neg.
  - move/Z.eqb_neq: Hm2 => Hm2.
    case Hm1 : (m1 =? 0).
    + move/Z.eqb_eq: Hm1 => ->. exact: cong_quot_best_m1_zero.
    + move/Z.eqb_neq: Hm1 => Hm1.
      exact: cong_quot_best_nonconstant_divisor_m1_nz.
Qed.
