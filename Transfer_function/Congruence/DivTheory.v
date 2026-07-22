(* DivTheory.v - [Z.div] (floor division) transfer function for the Congruence
   single-value abstraction: [cong_div] takes two congruences (r, m) and
   returns a congruence. Split out of Congruence.v.

   The operations themselves live in [OpsComp.v]; this file is proofs only. *)

(* STATUS: div (Z.div): best (cong_div_best) — exact in cases A/B/D1.
   The carry/pigeonhole helpers it shares with [QuotTheory.v]
   ([Z_div_add_carry], [exists_no_carry_step], [exists_carry_step],
   [carry_witnesses_divides_one]) stay in Congruence.v. *)

Require Import Abstraction AbstractLattice.
Require Import ssreflect ssrbool ssrfun.
Require Import BoundAbstraction.
Require Import AbstractionCombination.
Require Import BoundLattice.
Require Import autoreflect.
Require Import Tactics.
Require Import Stdlib.Bool.Bool.
Require Import QuadrivalentComp.
From Stdlib Require Import Lia. (* lia/nia; avoid Psatz which loads Reals axioms *)
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Congruence.
Require Import Transfer_function.Congruence.OpsComp.
Open Scope Z_scope.
Generalizable All Variables.

(** * Division. *)

(** Integer division does not preserve congruence structure in general;
    we identify the cases where a tight result exists:

    - Divide by the singleton {0}: Coq's [a / 0 = 0], so the concrete
      result is {0}, exactly represented by (0, 0).

    - Divide by a nonzero constant r2 with r2 ∣ m1: the concrete set is
      γ(r1/r2, m1/r2) exactly, by Z.div_add.

    - Otherwise: fall back to top (0, 1).

    Note: in the generic "r2 ∣ m1" case we no longer require r2 ∣ r1
    (Coq's [/] is [Z.div], which is defined even on non-multiples).
    Best-abstraction proofs below handle each case separately. *)

Lemma cong_div_sound:
  binary_overapproximation cong_ad cong_ad (WithBottom.ad cong_ad) cong_div
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div).
Proof.
  move=> a2 a1 c0 [c2 [c1 [Hc2_in_a2 [Hc1_in_a1 [Hc1_ne Hc0]]]]].
  move: a2 a1 Hc2_in_a2 Hc1_in_a1 => [ra ma] [rb mb] Ha Hb.
  rewrite /cong_div.
  have Htop (z : Z) : z ∈ γ[cong_ad] (0, 1).
  { unfold_set. apply Z.divide_1_l. }
  case Hmb: (mb =? 0); last first.
  { (* mb ≠ 0: dividend_zero if dividend is {0}, else top. *)
    move: Hmb => /Z.eqb_neq Hmb.
    case Hr1m1 : ((ma =? 0) && (ra =? 0)); last first.
    - (* nonconstant_divisor (top): NotBot (0, 1), γ = ℤ. *)
      simpl. move: Hc0 => <-. exact: Htop.
    - (* dividend_zero: c2 = 0 forces Z.div 0 c1 = 0 ∈ γ(0,0). *)
      move/andP: Hr1m1 => [/Z.eqb_eq Hma /Z.eqb_eq Hra].
      subst ra ma.
      move/gamma_singleton in Ha.
      simpl. move: Hc0 => <-. rewrite Ha Zdiv_0_l.
      by apply/gamma_singleton. }
  move: Hmb => /Z.eqb_eq Hmb.
  case Hrb: (rb =? 0).
  { (* divisor_zero: divisor set = {0}, but c1 ≠ 0 is required — contradiction. *)
    move: Hrb => /Z.eqb_eq Hrb. subst rb mb.
    move/gamma_singleton in Hb.
    by rewrite Hb in Hc1_ne. }
  move: Hrb => /Z.eqb_neq Hrb.
  case Hma_mod: (ma mod rb =? 0); last first.
  - (* const_pos/neg (top). *)
    simpl. move: Hc0 => <-. exact: Htop.
  - move: Hma_mod => /Z.eqb_eq Hma_mod.
    subst mb. move/gamma_singleton in Hb.
    unfold_set in Ha. move: Ha => [k Hk].
    have Hma_eq : ma = rb * (ma / rb) by have := Z.div_mod ma rb Hrb; lia.
    have Hc2 : c2 = ra + (k * (ma / rb)) * rb by nia.
    simpl. move: Hc0 => <-. rewrite Hc2 Hb (Z.div_add _ _ _ Hrb).
    unfold_set. exists k. lia.
Qed.

(** ** Total-semantics case lemmas (on [cong_ad]).

    Each branch of [cong_div]'s dispatch — keyed by the shape of the
    divisor and dividend — is proved here as a standalone
    [ExactlyRepresents] or [BestAbstraction] over the *total* collecting
    set. The [WithBottom] wrappers further below ([cong_div_best_*]) lift
    these to the partial (divisor ≠ 0) semantics that [cong_div_best]
    dispatches on; the [_total] suffix marks this total-set kernel. *)

(** Divisor is the constant {0}: the result set is {0}, best is (0,0). *)
Lemma cong_div_exact_divisor_zero_total (r1 m1 : Z) :
  ExactlyRepresents (A:=cong_ad) (0, 0)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (0, 0))).
Proof.
  split.
  - (* γ(0,0) ⊆ S *)
    move=> c. move/gamma_singleton => ->. exists r1, 0. split; [|split].
    + by exists 0; lia.
    + by apply/gamma_singleton.
    + exact: Zdiv_0_r.
  - (* S ⊆ γ(0,0) *)
    move=> c. unfold_set. move=> [c2 [c1 [_ [Hc1 Hdef]]]].
    move/gamma_singleton in Hc1.
    rewrite Hc1 Zdiv_0_r in Hdef. subst c.
    by apply/gamma_singleton.
Qed.

Lemma cong_div_best_divisor_zero_total (r1 m1 : Z) :
  BestAbstraction (A:=cong_ad) (0, 0)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (0, 0))).
Proof.
  apply: is_alpha_is_best_abstraction.
  apply: exact_is_is_alpha. exact: cong_div_exact_divisor_zero_total.
Qed.

(** Constant divisor r2 ≠ 0 with r2 ∣ m1: then γ(r1,m1) / {r2} =
    γ(r1/r2, m1/r2) exactly. *)
Lemma cong_div_exact_const_divides_total (r1 m1 r2 : Z) :
  r2 <> 0 -> (r2 | m1) ->
  ExactlyRepresents (A:=cong_ad) (r1 / r2, m1 / r2)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hdivs.
  have Hm1_eq : m1 = (m1 / r2) * r2.
  { case: Hdivs => q ->. by rewrite (Z.div_mul _ _ Hr2). }
  have Hdiv_eq : forall k, (r1 + k * m1) / r2 = r1 / r2 + k * (m1 / r2).
  { move=> k.
    have -> : r1 + k * m1 = r1 + (k * (m1 / r2)) * r2 by nia.
    exact: Z.div_add _ _ _ Hr2. }
  split.
  - (* γ(r1/r2, m1/r2) ⊆ S: given c = r1/r2 + k·(m1/r2), produce
       c2 = r1 + k·m1, c1 = r2 with Z.div c2 r2 = c. *)
    move=> c. unfold_set. move=> [k Hk].
    exists (r1 + k * m1), r2. split; [|split].
    + by exists k; lia.
    + by apply/gamma_singleton.
    + rewrite Hdiv_eq. lia.
  - (* S ⊆ γ(r1/r2, m1/r2): unfold Z.div via Z.div_add. *)
    move=> c. unfold_set.
    move=> [c2 [c1 [[k Hk] [Hc1 Hdef]]]].
    move/gamma_singleton in Hc1. subst c1.
    have Hc2 : c2 = r1 + k * m1 by lia. subst c2.
    by exists k; rewrite -Hdef Hdiv_eq; lia.
Qed.

Lemma cong_div_best_const_divides_total (r1 m1 r2 : Z) :
  r2 <> 0 -> (r2 | m1) ->
  BestAbstraction (A:=cong_ad) (r1 / r2, m1 / r2)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hdivs.
  apply: is_alpha_is_best_abstraction.
  apply: exact_is_is_alpha. exact: cong_div_exact_const_divides_total.
Qed.

(** ** Constant divisor (positive) not dividing m1. Top (0, 1) is the
    best abstraction, but NOT γ-exact: the quotient set
    [{(r1+k·m1)/r2 : k ∈ ℤ}] generally skips integers.

    Proof is constructive (no classical reasoning) so the infrastructure
    ports cleanly to a future Z.quot variant.

    High-level strategy. Let q := m1/r2 and rm := m1 mod r2 (so 0 < rm < r2
    because ¬(r2 ∣ m1)). For any overapproximating abstraction (r', m'), we
    derive m' ∣ 1 — which forces m' = ±1 and hence (0,1) ⊑ (r',m').

    Fix k and look at V(k) := (r1 + k·m1)/r2. Consecutive gaps
    V(k+1) − V(k) equal q + carry(k), where carry(k) ∈ {0, 1}. All gaps
    are divisible by m' (since m' divides each V(k) − r'). So if we can
    exhibit one step with carry = 0 (giving m' ∣ q) and one step with
    carry = 1 (giving m' ∣ q+1), then m' ∣ (q+1) − q = 1.

    Existence of both kinds of step follows from the telescoping sum
    V(r2) − V(0) = m1 = r2·q + rm with 0 < rm < r2: the total carry across
    r2 steps equals rm, which is neither 0 nor r2, so some step carries and
    some doesn't. Helpers [exists_no_carry_step] and [exists_carry_step]
    produce the witnesses constructively via [natlike_ind]. *)


(** Main const-positive lemma: top is best when the divisor is a known
    nonzero positive constant and does not divide m1. *)

Lemma cong_div_best_const_pos_total r1 m1 r2 :
  0 < r2 -> ~(r2 | m1) ->
  BestAbstraction (A:=cong_ad) (0, 1)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  split.
  - move=> c _. unfold_set. apply: Z.divide_1_l.
  - move=> [r' m'] HS.
    have V_in : forall k, 0 <= k <= r2 -> (m' | (r1 + k*m1) / r2 - r').
    { move=> k _.
      have Hmem : (r1 + k*m1) / r2 ∈ γ[cong_ad] (r', m').
      { apply: HS. unfold_set. exists (r1 + k*m1), r2.
        split; [by exists k; lia
               |split; [by exists 0; lia | reflexivity]]. }
      by unfold_set in Hmem. }
    have Hone := carry_witnesses_divides_one _ _ _ _ _ Hr2 Hnd V_in.
    split; first exact: Hone.
    apply: Z.divide_trans Hone _. exact: Z.divide_1_l.
Qed.

(** Constant negative divisor not dividing m1, by reduction to the positive case.

    Key observation: for c ≠ 0, [Z.div_opp_opp] gives (-a)/(-c) = a/c.
    So for r2 < 0, the quotient set
      {c1/r2 : c1 ∈ γ(r1, m1)}
    equals (via the bijection c1 ↔ -c1)
      {c1'/(-r2) : c1' ∈ γ(-r1, m1)}.
    The latter is exactly the case-C-positive set for (−r1, m1) divided by
    (−r2, 0). We transport [BestAbstraction] across this set equality. *)
Lemma cong_div_best_const_neg_total r1 m1 r2 :
  r2 < 0 -> ~(r2 | m1) ->
  BestAbstraction (A:=cong_ad) (0, 1)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  have Hr2_ne : r2 <> 0 by lia.
  have Hr2' : 0 < -r2 by lia.
  have Hnd' : ~(-r2 | m1).
  { move=> [k Hk]. apply: Hnd. by exists (-k); lia. }
  have HC := cong_div_best_const_pos_total (-r1) m1 (-r2) Hr2' Hnd'.
  have Hset : forall z,
    z ∈ collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))
    <-> z ∈ collecting_binary_forward Z.div (γ[cong_ad] (-r1, m1)) (γ[cong_ad] (-r2, 0)).
  { move=> z. split.
    - move=> H. unfold_set in H. move: H => [c1 [c2 [Hc1 [Hc2 Hd]]]].
      unfold_set. exists (-c1), (-c2). split; [|split].
      + unfold_set in Hc1. unfold_set. case: Hc1 => k Hk. by exists (-k); lia.
      + move/gamma_singleton :Hc2 => ->.
        by exists 0; lia.
      + have Hc2eq : c2 = r2 by move/gamma_singleton :Hc2.
        rewrite Hc2eq. rewrite (Z.div_opp_opp _ _ Hr2_ne).
        by rewrite -Hc2eq.
    - move=> H. unfold_set in H. move: H => [c1' [c2' [Hc1' [Hc2' Hd]]]].
      unfold_set. exists (-c1'), (-c2'). split; [|split].
      + unfold_set in Hc1'. unfold_set. case: Hc1' => k Hk. by exists (-k); lia.
      + move/gamma_singleton :Hc2' => ->.
        by exists 0; lia.
      + have Hc2eq : c2' = -r2 by move/gamma_singleton :Hc2'.
        have Hne : -r2 <> 0 by lia.
        rewrite Hc2eq in Hd. rewrite Hc2eq.
        by rewrite (Z.div_opp_opp _ _ Hne). }
  case: HC => HO HB. split.
  - move=> c Hc. apply: HO. by apply/Hset.
  - move=> [r' m'] Ha'. apply: HB.
    move=> c Hc. apply: Ha'. by apply/Hset.
Qed.

(** ** Non-constant divisor (m2 ≠ 0), split on the dividend.

    Dividend exactly {0} (r1 = m1 = 0): result = {0}, best (0,0).
    Dividend non-{0}: result contains {0, -1}, best (0,1). *)

(** Dividend exactly {0} is actually γ-exact: γ(r1,m1) = {0} forces c1 = 0,
    so every element of S is Z.div 0 c2 = 0, and conversely 0 is reached by
    picking c1 = 0 and any c2 ∈ γ(r2,m2). Thus S = {0} = γ(0,0). *)
Lemma cong_div_exact_dividend_zero_total r2 m2 :
  m2 <> 0 ->
  ExactlyRepresents (A:=cong_ad) (0, 0)
    (collecting_binary_forward Z.div (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  split.
  - (* γ(0,0) ⊆ S: γ(0,0) = {0}, and 0 ∈ S witnessed by c1 = 0, c2 = r2. *)
    move=> c. move/gamma_singleton => ->.
    unfold_set. exists 0, r2. split; [by apply/gamma_singleton|].
    split; [by exists 0; lia|]. by rewrite Zdiv_0_l.
  - (* S ⊆ γ(0,0): any z ∈ S has z = Z.div c1 c2 with c1 ∈ γ(0,0) = {0},
       so c1 = 0 and z = 0/c2 = 0 ∈ γ(0,0). *)
    move=> c Hc. unfold_set in Hc. case: Hc => [c1 [c2 [Ha [_ Hd]]]].
    move/gamma_singleton in Ha.
    rewrite -Hd Ha Zdiv_0_l. by apply/gamma_singleton.
Qed.

Lemma cong_div_best_dividend_zero_total r2 m2 :
  m2 <> 0 ->
  BestAbstraction (A:=cong_ad) (0, 0)
    (collecting_binary_forward Z.div (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  apply: is_alpha_is_best_abstraction.
  apply: exact_is_is_alpha. exact: cong_div_exact_dividend_zero_total.
Qed.

(** Non-constant divisor (m2 ≠ 0) with dividend not exactly {0}. Top (0, 1)
    is best but NOT γ-exact (the quotient set is typically bounded, e.g.
    {r1/c : c ∈ γ(r2,m2)} for m1 = 0 is finite).

    Strategy: force m' ∣ 1 by exhibiting BOTH 0 and −1 in the quotient set.
    Pick any nonzero c1 ∈ γ(r1,m1). Since γ(r2,m2) is an arithmetic
    progression with step |m2| ≥ 1, we can reach divisors of arbitrarily
    large magnitude on both sides: c2p := r2 + A·sgn(m2)·m2 > |c1| and
    c2n := r2 − A·sgn(m2)·m2 < −|c1| (for A := |c1| + |r2| + 1).
    Then c1/c2p and c1/c2n realize {0, −1}:
      - if c1 > 0: c1/c2p = 0 (small nonneg dividend); c1/c2n = −1.
      - if c1 < 0: c1/c2p = −1; c1/c2n = 0 (by symmetric bounds).
    From m' ∣ (0 − r') and m' ∣ (−1 − r'), we get m' ∣ 1. *)
Lemma cong_div_best_nonconstant_divisor_total r1 m1 r2 m2 :
  m2 <> 0 -> (r1 <> 0 \/ m1 <> 0) ->
  BestAbstraction (A:=cong_ad) (0, 1)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2 Hne.
  split.
  - (* γ(0,1) = ℤ, so S ⊆ γ(0,1) trivially. *)
    move=> c _. unfold_set. exact: Z.divide_1_l.
  - move=> [r' m'] HS.
    (* Step 1: pick c1 ∈ γ(r1,m1) with c1 ≠ 0. *)
    have [c1 [Hc1_in Hc1_ne]] : exists c1, c1 ∈ γ[cong_ad] (r1, m1) /\ c1 <> 0.
    { case: (Z.eq_dec r1 0) => [Hr1|Hr1].
      - (* r1 = 0; then m1 ≠ 0 *)
        have Hm1 : m1 <> 0 by case: Hne => //; rewrite Hr1.
        exists m1. split; last exact Hm1.
        unfold_set. exists 1. lia.
      - exists r1. split; last exact Hr1.
        unfold_set. by exists 0; lia. }
    (* Step 2: construct c2p, c2n ∈ γ(r2,m2) with c2p > |c1|, c2n < -|c1|. *)
    pose A := Z.abs c1 + Z.abs r2 + 1.
    have HA1 : 1 <= A.
    { rewrite /A. have := Z.abs_nonneg c1. have := Z.abs_nonneg r2. lia. }
    have Hm2_abs : 1 <= Z.abs m2.
    { have := Z.abs_nonneg m2.
      case: (Z.abs_spec m2) => [[_ ->]|[_ ->]]; lia. }
    have Hsgn_mul : Z.sgn m2 * m2 = Z.abs m2.
    { have := Z.abs_sgn m2. nia. }
    pose c2p := r2 + A * Z.sgn m2 * m2.
    pose c2n := r2 - A * Z.sgn m2 * m2.
    have Hc2p_eq : c2p = r2 + A * Z.abs m2.
    { rewrite /c2p. have := Hsgn_mul. nia. }
    have Hc2n_eq : c2n = r2 - A * Z.abs m2.
    { rewrite /c2n. have := Hsgn_mul. nia. }
    have Hc1_abs : Z.abs c1 <= c1 \/ c1 <= - Z.abs c1.
    { case: (Z.abs_spec c1); lia. }
    have Hr2_abs : - Z.abs r2 <= r2 <= Z.abs r2.
    { case: (Z.abs_spec r2); lia. }
    have Hc2p_big : Z.abs c1 < c2p.
    { rewrite Hc2p_eq /A. nia. }
    have Hc2n_small : c2n < - Z.abs c1.
    { rewrite Hc2n_eq /A. nia. }
    have Hc2p_pos : 0 < c2p.
    { have := Z.abs_nonneg c1. lia. }
    have Hc2n_neg : c2n < 0.
    { have := Z.abs_nonneg c1. lia. }
    have Hc2p_in : c2p ∈ γ[cong_ad] (r2, m2).
    { unfold_set. exists (A * Z.sgn m2). rewrite /c2p. ring. }
    have Hc2n_in : c2n ∈ γ[cong_ad] (r2, m2).
    { unfold_set. exists (- (A * Z.sgn m2)). rewrite /c2n. ring. }
    (* Step 3: show 0 ∈ S and -1 ∈ S *)
    have Hc1_bounds : - c2p < c1 < c2p.
    { have := Z.abs_nonneg c1. case: (Z.abs_spec c1); lia. }
    have H0_in : 0 ∈ collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)).
    { case: (Z_lt_le_dec 0 c1) => Hsgn.
      - (* c1 > 0: c1/c2p = 0 *)
        unfold_set. exists c1, c2p. split; first done. split; first done.
        apply: Z.div_small. lia.
      - (* c1 < 0: c1/c2n = 0 *)
        unfold_set. exists c1, c2n. split; first done. split; first done.
        have Hc2n_ne : c2n <> 0 by lia.
        apply/Z.div_small_iff => //. right. lia. }
    have Hm1_in : (-1) ∈ collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)).
    { case: (Z_lt_le_dec 0 c1) => Hsgn.
      - (* c1 > 0, c2n < 0 < c1 < -c2n: c1/c2n = -1 *)
        unfold_set. exists c1, c2n. split; first done. split; first done.
        symmetry. apply: (Z.div_unique _ _ (-1) (c1 + c2n)); lia.
      - (* c1 < 0, c2p > -c1 > 0: c1/c2p = -1 *)
        unfold_set. exists c1, c2p. split; first done. split; first done.
        symmetry. apply: (Z.div_unique _ _ (-1) (c1 + c2p)); lia. }
    (* Step 4: both 0 and -1 lie in γ(r',m'), and their difference is 1. *)
    have := HS _ H0_in. unfold_set => H0'.    (* m' | 0 - r' *)
    have := HS _ Hm1_in. unfold_set => Hm1'.  (* m' | -1 - r' *)
    have Hone : (m' | 1).
    { have Hd : (m' | (0 - r') - (-1 - r')) by apply: Z.divide_sub_r.
      have -> : 1 = (0 - r') - (-1 - r') by ring.
      exact Hd. }
    (* order (0, 1) (r', m') = (m' | 1) ∧ (m' | 0 - r'); both established. *)
    split; first exact: Hone.
    exact: H0'.
Qed.

(** ** Lifting helpers to [WithBottom]-wrapped best abstractions.

    The generic lemmas [WithBottom.WithBottom.BestAbstraction_NotBot],
    [WithBottom.BestAbstraction_Bot] (in [AbstractionCombination]) and
    [best_abstraction_equiv] (in [Abstraction]) do the heavy lifting.
    Below we add only a partial/total set-equivalence tailored to
    [collecting_binary_forward(_partial)] when the divisor set has no 0. *)

Lemma collecting_div_partial_total_nz (S2 S1 : propset Z) :
  (forall c, c ∈ S1 -> c <> 0) ->
  collecting_binary_forward Z.div S2 S1 ⊆⊇
  collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div S2 S1.
Proof.
  move=> Hnz. split.
  - move=> c [c2 [c1 [Hc2 [Hc1 Hd]]]].
    exists c2, c1. split; [|split; [|split]]; by [|apply: Hnz].
  - by move=> c [c2 [c1 [Hc2 [Hc1 [_ Hd]]]]]; exists c2, c1.
Qed.

(** ** Best-abstraction case lemmas lifted to [WithBottom]. *)

Lemma cong_div_best_divisor_zero (r1 m1 : Z) :
  BestAbstraction (A:=WithBottom.ad cong_ad) WithBottom.Bot
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (0, 0))).
Proof.
  apply: WithBottom.BestAbstraction_Bot.
  move=> c [c2 [c1 [_ [Hc1 [Hne _]]]]].
  unfold_set in Hc1. case: Hc1 => [k Hk].
  have : c1 = 0 by nia.
  by move/Hne.
Qed.

(** Shared witness that r1/r2 is in the partial set when r2 ≠ 0. *)
Local Lemma const_divisor_elem r1 m1 r2 :
  r2 <> 0 ->
  (r1 / r2) ∈ collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
                (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0)).
Proof.
  move=> Hr2. exists r1, r2.
  split; [by exists 0; lia|].
  split; [by exists 0; lia|].
  split; [exact Hr2 | reflexivity].
Qed.

Lemma cong_div_best_const_divides (r1 m1 r2 : Z) :
  r2 <> 0 -> (r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (r1 / r2, m1 / r2))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hdiv.
  have Hnz : forall c, c ∈ γ[cong_ad] (r2, 0) -> c <> 0.
  { move=> c. move/gamma_singleton => ->. exact: Hr2. }
  have Heq := collecting_div_partial_total_nz _ _ Hnz.
  apply: WithBottom.BestAbstraction_NotBot; first by exists (r1 / r2); exact: const_divisor_elem.
  apply: best_abstraction_equiv; last exact: Heq.
  exact: cong_div_best_const_divides_total.
Qed.

Lemma cong_div_best_const_pos (r1 m1 r2 : Z) :
  0 < r2 -> ~(r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  have Hnz : forall c, c ∈ γ[cong_ad] (r2, 0) -> c <> 0.
  { move=> c. move/gamma_singleton => ->. lia. }
  have Heq := collecting_div_partial_total_nz _ _ Hnz.
  apply: WithBottom.BestAbstraction_NotBot;
    first by exists (r1 / r2); apply: const_divisor_elem; lia.
  apply: best_abstraction_equiv; last exact: Heq.
  exact: cong_div_best_const_pos_total.
Qed.

Lemma cong_div_best_const_neg (r1 m1 r2 : Z) :
  r2 < 0 -> ~(r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  have Hnz : forall c, c ∈ γ[cong_ad] (r2, 0) -> c <> 0.
  { move=> c. move/gamma_singleton => ->. lia. }
  have Heq := collecting_div_partial_total_nz _ _ Hnz.
  apply: WithBottom.BestAbstraction_NotBot;
    first by exists (r1 / r2); apply: const_divisor_elem; lia.
  apply: best_abstraction_equiv; last exact: Heq.
  exact: cong_div_best_const_neg_total.
Qed.

(** Dividend = {0}. The total and partial sets differ when 0 ∈ γ(r2,m2)
    (total has 0 from 0/0, partial has 0 from 0/nonzero). Both are exactly
    {0} under m2 ≠ 0, so the transport is direct. *)
Lemma cong_div_best_dividend_zero (r2 m2 : Z) :
  m2 <> 0 ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 0))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  (* γ(r2, m2) is infinite and has elements ≠ 0. *)
  have [c1 [Hc1_in Hc1_ne]] : exists c1, c1 ∈ γ[cong_ad] (r2, m2) /\ c1 <> 0.
  { case: (Z.eq_dec r2 0) => Hr2.
    - exists (r2 + m2). split; last by rewrite Hr2; lia.
      unfold_set. by exists 1; lia.
    - exists r2. split; last exact Hr2.
      unfold_set. by exists 0; lia. }
  have Heq : collecting_binary_forward Z.div (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))
             ⊆⊇
             collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
               (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2)).
  { split.
    - move=> c [c2 [c1' [Ha [Hb Hd]]]].
      move/gamma_singleton in Ha.
      subst c2. rewrite Zdiv_0_l in Hd. subst c.
      (* c = 0 is still in partial: witness c1 (nonzero). *)
      exists 0, c1. split; [by apply/gamma_singleton|].
      split; [exact Hc1_in|]. split; [exact Hc1_ne|].
      exact: Zdiv_0_l.
    - by move=> c [c2 [c1' [Ha [Hb [_ Hd]]]]]; exists c2, c1'. }
  apply: WithBottom.BestAbstraction_NotBot.
  - exists 0. apply: (proj1 Heq).
    exists 0, c1. split; [by exists 0; lia|].
    split; [exact Hc1_in| exact: Zdiv_0_l].
  - apply: best_abstraction_equiv; last exact: Heq.
    exact: cong_div_best_dividend_zero_total.
Qed.

(** Non-constant divisor. When [0 ∈ γ(r2,m2)] the total and partial
    sets differ only in whether [0] comes from a [c2 = 0] pair. We build
    a partial-set witness of [0] by picking any c1 ∈ γ(r1,m1) and a
    nonzero c2 ∈ γ(r2,m2) of matching sign and larger magnitude; the
    quotient is then forced to [0]. With that, partial ⊆⊇ total. *)
Lemma cong_div_d2_partial_total r1 m1 r2 m2 :
  m2 <> 0 ->
  collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)) ⊆⊇
  collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
    (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)).
Proof.
  move=> Hm2.
  have Hsgn_mul : Z.sgn m2 * m2 = Z.abs m2 by have := Z.abs_sgn m2; nia.
  have Hm2_abs : 1 <= Z.abs m2.
  { have Hm2' : m2 <> 0 := Hm2.
    case: (Z.abs_spec m2) => [[? ->]|[? ->]]; lia. }
  split; last by move=> c [c2 [c1 [Ha [Hb [_ Hd]]]]]; exists c2, c1.
  move=> c [c2 [c1 [Ha [Hb Hd]]]].
  case: (Z.eq_dec c1 0) => [Hc1_0|Hnz]; last by exists c2, c1.
  subst c1. rewrite Zdiv_0_r in Hd. subst c.
  (* Rebuild 0 via a nonzero c1' of same sign as c2 with |c1'| > |c2|. *)
  pose A := Z.abs c2 + Z.abs r2 + 1.
  pose s := Z.sgn c2 + (if c2 =? 0 then 1 else 0).  (* ensures s ≠ 0 *)
  pose c1' := r2 + (s * A) * Z.sgn m2 * m2.
  have HA : 1 <= A.
  { rewrite /A. have := Z.abs_nonneg c2. have := Z.abs_nonneg r2. lia. }
  have Hs_val : s = 1 \/ s = -1.
  { rewrite /s. case: (Z.eqb_spec c2 0) => [->|Hne] /=.
    - by left.
    - case: (Z.lt_trichotomy c2 0) => [Hl|[Hz|Hp]]; [right|done|left].
      + by rewrite Z.sgn_neg //; lia.
      + by rewrite Z.sgn_pos //; lia. }
  have Hs_sgn : (s = 1 -> 0 <= c2) /\ (s = -1 -> c2 <= 0).
  { rewrite /s. case: (Z.eqb_spec c2 0) => [->|Hne] /=.
    - by split; [|lia].
    - have := Z.sgn_null_iff c2. have := Z.sgn_pos_iff c2.
      have := Z.sgn_neg_iff c2.
      case: (Z.sgn c2); lia. }
  have Hr2_abs : - Z.abs r2 <= r2 <= Z.abs r2 by case: (Z.abs_spec r2); lia.
  have Hc2_abs : - Z.abs c2 <= c2 <= Z.abs c2 by case: (Z.abs_spec c2); lia.
  have Hc1'_eq : c1' = r2 + s * A * Z.abs m2.
  { rewrite /c1'. have := Hsgn_mul. nia. }
  have Hc1'_ne : c1' <> 0 by rewrite Hc1'_eq /A; case: Hs_val => ->; nia.
  have Hc1'_in : c1' ∈ γ[cong_ad] (r2, m2).
  { unfold_set. by exists (s * A * Z.sgn m2); rewrite /c1'; ring. }
  exists c2, c1'. split; first done. split; first done. split; first exact Hc1'_ne.
  apply/Z.div_small_iff => //. rewrite Hc1'_eq /A.
  case: Hs_val => Hs.
  - left. split; [apply (proj1 Hs_sgn); exact Hs | rewrite Hs; nia].
  - right. split; [rewrite Hs; nia | apply (proj2 Hs_sgn); exact Hs].
Qed.

Lemma cong_div_best_nonconstant_divisor (r1 m1 r2 m2 : Z) :
  m2 <> 0 -> (r1 <> 0 \/ m1 <> 0) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2 Hne.
  have Heq := cong_div_d2_partial_total r1 m1 r2 m2 Hm2.
  (* Non-emptiness witness: total contains e.g. r1/r2, hence so does partial. *)
  apply: WithBottom.BestAbstraction_NotBot.
  - exists (r1 / r2). apply: (proj1 Heq).
    exists r1, r2. split; [by exists 0; lia|].
    split; [by exists 0; lia| reflexivity].
  - apply: best_abstraction_equiv; last exact: Heq.
    exact: cong_div_best_nonconstant_divisor_total.
Qed.

(** Aggregate: [cong_div] is a best abstraction for [Z.div] under
    partial semantics (divisor ≠ 0). Dispatches on the [if]-structure. *)
Lemma cong_div_best :
  binary_best cong_ad cong_ad (WithBottom.ad cong_ad) cong_div
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div).
Proof.
  move=> a2 a1.
  move: a2 a1 => [r1 m1] [r2 m2].
  rewrite /cong_div.
  case Hm2 : (m2 =? 0).
  - move/Z.eqb_eq: Hm2 => ->.
    case Hr2 : (r2 =? 0).
    + move/Z.eqb_eq: Hr2 => ->. exact: cong_div_best_divisor_zero.
    + move/Z.eqb_neq: Hr2 => Hr2.
      case Hdiv : (m1 mod r2 =? 0).
      * move/Z.eqb_eq: Hdiv => Hdiv.
        apply: cong_div_best_const_divides => //.
        by apply/Z.mod_divide.
      * move/Z.eqb_neq: Hdiv => Hdiv.
        have Hnd : ~(r2 | m1).
        { move=> H. apply: Hdiv. by apply/Z.mod_divide. }
        case: (Z_lt_le_dec 0 r2) => Hr2sgn.
        -- exact: cong_div_best_const_pos.
        -- have Hr2lt : r2 < 0 by lia.
           exact: cong_div_best_const_neg.
  - move/Z.eqb_neq: Hm2 => Hm2.
    case Hcond : ((m1 =? 0) && (r1 =? 0)).
    + move/andP: Hcond => [/Z.eqb_eq -> /Z.eqb_eq ->].
      exact: cong_div_best_dividend_zero.
    + apply: cong_div_best_nonconstant_divisor => //.
      case: (Z.eq_dec r1 0) => [Hr1|Hr1]; last by left.
      right. case: (Z.eq_dec m1 0) => [Hm1|//].
      exfalso. move: Hcond. by rewrite Hr1 Hm1.
Qed.
