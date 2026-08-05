(* QuotTheory.v - [Z.quot] (truncating division) forward transfer function for
   the ZInterval single-value abstraction. We try to use the calculational style
   of abstract interpretation whenever possible.

   STATUS: quot (Z.quot): best in all 9 sign cases (interval_quot_best).  Six of
   them are α-complete for arbitrary operand sets
   (interval_quot_*_alpha_complete): the four quarters and the two
   across-*dividend* cases.  The three across-*divisor* cases are only [_best],
   and provably cannot be strengthened — [quot_across_no_alpha_complete] rules
   out any α-complete transfer function of two intervals.  What they are
   α-complete relative to is a supplied split of the divisor at its extremal
   nonzero values (interval_quot_*_across_split_alpha_complete), which is the
   entry point for interval×congruence (or others, like known bits).

   Proof strategy: The four *quarter* cases (dividend and divisor each of
   definite sign) are proved α-complete (for arbitrary concrete sets, not only
   at concretizations ). The *across* cases (one operand crossing 0) are derived
   from them by splitting the collecting semantics at 0 (dividend) or at ±1
   (divisor) and joining.  Dispatching on the typed [classify_divisor] gives the
   chain's [interval_quot_unopt_best]; the extracted, optimized version
   [ZIntervalOps.interval_quot] is then proved equal to the chain
   ([interval_quot_unopt_eq]) and so inherits it as [interval_quot_best].

   Some parts of the proof need dependent types because we want to prove that
   the code does not trigger any division by zero error when extracted.

   Divisor sign facts come from the typed [classify_divisor] payload
   ([pos_interval] / [neg_interval] / [across_interval]), not from after-the-
   fact inversion lemmas. MAYBE: Change this as this may make the extracted code
   more efficient? *)

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
(* [Zquot]'s unconditional [Zquot_opp_l] / [Zquot_opp_r] / [Zquot_0_l], which
   the [Z.] namesakes state only for a non-zero divisor. *)
Require Import Stdlib.ZArith.Zquot.
Require Import ZInterval.
Require Import ZIntervalTheory.
Require Import PrimitiveTheory.
Require Import Transfer_function.ZInterval.ZIntervalOps.
Require Import Transfer_function.ZInterval.OppTheory.
Open Scope Z_scope.
Generalizable All Variables.

Section Interval_quot.

(** * Collecting semantics.

    [Z.quot] is partial (the divisor is non-zero), so the forward collecting
    semantics excludes division by zero; the result is empty when every divisor
    is zero.  [collecting_quot] and the set-level facts that are not specific
    to this transfer function live in [PrimitiveTheory.v], beside the
    [Primitives.quot_non_zero] they collect.  What follows here is only what
    the sign splits and the α-completeness proofs need. *)

(** * Negation transport: [collecting_quot] commutes with [Z.opp].

    Negation commutes with [collecting_quot] on either argument, and the two
    together cancel.  These are the side conditions for [is_alpha_opp_iff] to
    transport α-completeness from the positive/positive quarter; C99 truncation
    gives [(-a) ÷ b = -(a ÷ b)], [a ÷ (-b) = -(a ÷ b)], [(-a) ÷ (-b) = a ÷ b]. *)

Lemma collecting_quot_opp_l (T2 T1 : ℘ Z) :
  collecting_quot {[ z | -z ∈ T2 ]} T1 ⊆⊇
  {[ z | -z ∈ collecting_quot T2 T1 ]}.
Proof.
  unfold_set_equiv => c; split;
    move=> [c2 [c1 [Hc2 [Hc1 [Hne Heq]]]]];
    exists (- c2), c1; unfold_set;
    rewrite ?Z.opp_involutive (Z.quot_opp_l c2 c1 Hne);
    by repeat split => //; lia.
Qed.

Lemma collecting_quot_opp_r (T2 T1 : ℘ Z) :
  collecting_quot T2 {[ z | -z ∈ T1 ]} ⊆⊇
  {[ z | -z ∈ collecting_quot T2 T1 ]}.
Proof.
  unfold_set_equiv => c; split;
    move=> [c2 [c1 [Hc2 [Hc1 [Hne Heq]]]]];
    exists c2, (- c1); unfold_set;
    rewrite ?Z.opp_involutive (Z.quot_opp_r c2 c1 Hne);
    by repeat split => //; lia.
Qed.

(** Negating both operands is negating each in turn. *)
Lemma collecting_quot_opp_both (T2 T1 : ℘ Z) :
  collecting_quot {[ z | -z ∈ T2 ]} {[ z | -z ∈ T1 ]} ⊆⊇
  collecting_quot T2 T1.
Proof.
  transitivity {[ z | -z ∈ collecting_quot T2 {[ z | -z ∈ T1 ]} ]};
    first exact: collecting_quot_opp_l.
  exact: (propset_opp_equiv_inv _ _ (collecting_quot_opp_r T2 T1)).
Qed.

(** * Splitting the collecting semantics at 0 / ±1.

    These set-level equivalences are the primitives the across cases compose
    with [is_alpha_join_split].  Both are instances of the generic
    [collecting_binary_forward_partial_split_zero_{l,strict_r}]
    ([ZIntervalTheory.v]); each quot-named lemma below only instantiates the
    partiality predicate [fun _ c1 => c1 <> 0] and — for the divisor — supplies
    the [c1 <> 0] covering premise that [P] gives it.

    The two are not symmetric, and the asymmetry is the whole reason division
    behaves differently in its two operands.  Splitting the dividend at 0 needs
    nothing about intervals — every integer is non-positive or non-negative —
    so it holds for an *arbitrary* dividend set.  Splitting the divisor has to
    cut away 0, and *which* divisors nearest zero a set contains is not
    something its interval records — hence the failure of α-completeness across
    the divisor ([quot_across_no_alpha_complete], at the end of this file).
    [collecting_quot_split_divisor_set] therefore cuts at [< 0] / [> 0], which
    is legitimate only because the partiality has already dropped the zero
    divisors; the ±1 form an interval needs is [gamma_itv_neg_half] /
    [gamma_itv_pos_half] below. *)

Lemma collecting_quot_split_dividend (S2 S1 : propset Z) :
  collecting_quot S2 S1 ⊆⊇
  collecting_quot {[ z | z ∈ S2 /\ z <= 0 ]} S1 ∪
  collecting_quot {[ z | z ∈ S2 /\ 0 <= z ]} S1.
Proof.
  exact: (collecting_binary_forward_partial_split_zero_l (fun _ c1 => c1 <> 0) Z.quot S2 S1).
Qed.

(** The sign halves of a zero-crossing interval's γ *are* the γ of its ∓1-capped
    halves.  This is what makes the interval-only case the [m := -1], [p := 1]
    instance of the split lemmas below. *)
Lemma gamma_itv_neg_half (l h : WithTop.with_top Z) :
  high_pos h ->
  γ[itv] (l, WithTop.NotTop (-1)) ⊆⊇ {[ z | z ∈ γ[itv] (l, h) /\ z < 0 ]}.
Proof.
  move=> Hh; split=> z; case: l => [|l]; case: h Hh => [|h] Hh;
    unfold_set; simpl in *; move=> *; repeat split; lia.
Qed.

Lemma gamma_itv_pos_half (l h : WithTop.with_top Z) :
  low_neg l ->
  γ[itv] (WithTop.NotTop 1, h) ⊆⊇ {[ z | z ∈ γ[itv] (l, h) /\ 0 < z ]}.
Proof.
  move=> Hl; split=> z; case: l Hl => [|l] Hl; case: h => [|h];
    unfold_set; simpl in *; move=> *; repeat split; lia.
Qed.

(** The two halves packaged as the three facts every across-divisor proof
    needs of each: the half contains the extremal nonzero divisor ∓1, it is
    non-bottom, and it best-abstracts the corresponding sign-restricted part
    of γ.  Bundled because the three are always wanted together. *)
Lemma across_neg_half_alpha (l h : WithTop.with_top Z) :
  low_neg l -> high_pos h ->
  (-1) ∈ γ[itv] (l, h)
  /\ non_bottom (l, WithTop.NotTop (-1))
  /\ IsAlpha (A:=itv) (l, WithTop.NotTop (-1))
       {[ z | z ∈ γ[itv] (l, h) /\ z < 0 ]}.
Proof.
  move=> Hl Hh.
  have Hm1 : (-1) ∈ γ[itv] (l, h)
    by move: Hl Hh; case: l => [|?]; case: h => [|?];
       unfold_set; simpl; repeat split=> //; lia.
  have Hnb := across_neg_half_non_bottom l Hl.
  split; first exact: Hm1. split; first exact: Hnb.
  apply: (is_alpha_set_equiv _ _ _ (gamma_itv_neg_half l h Hh)).
  exact: (non_bottom_is_alpha_gamma _ Hnb).
Qed.

Lemma across_pos_half_alpha (l h : WithTop.with_top Z) :
  low_neg l -> high_pos h ->
  1 ∈ γ[itv] (l, h)
  /\ non_bottom (WithTop.NotTop 1, h)
  /\ IsAlpha (A:=itv) (WithTop.NotTop 1, h)
       {[ z | z ∈ γ[itv] (l, h) /\ 0 < z ]}.
Proof.
  move=> Hl Hh.
  have Hp1 : 1 ∈ γ[itv] (l, h)
    by move: Hl Hh; case: l => [|?]; case: h => [|?];
       unfold_set; simpl; repeat split=> //; lia.
  have Hnb := across_pos_half_non_bottom h Hh.
  split; first exact: Hp1. split; first exact: Hnb.
  apply: (is_alpha_set_equiv _ _ _ (gamma_itv_pos_half l h Hl)).
  exact: (non_bottom_is_alpha_gamma _ Hnb).
Qed.

(** Splitting the divisor by sign, on arbitrary sets.  It works only because
    [collecting_quot] has already discarded the zero divisors, and because it
    cuts at [< 0] / [> 0] rather than at ∓1.  The ∓1 version cannot be stated
    this way: which integers nearest zero a set contains is not something the
    set's *interval* records. *)
Lemma collecting_quot_split_divisor_set (S2 S1 : propset Z) :
  collecting_quot S2 S1 ⊆⊇
  collecting_quot S2 {[ z | z ∈ S1 /\ z < 0 ]} ∪
  collecting_quot S2 {[ z | z ∈ S1 /\ 0 < z ]}.
Proof.
  exact: (collecting_non_zero_split_zero_strict_r Z.quot S2 S1).
Qed.

(** * The arithmetic core: positive dividend / strictly positive divisor.

    This is the one place the [Z.quot] arithmetic lives.  The result bounds are
    [quot_bound l2 h1] (low ÷ high) and [quot_bound h2 l1] (high ÷ low): the
    quotient is monotone in the dividend and antitone in a positive divisor, so
    the infimum is attained at the smallest dividend and largest divisor, the
    supremum at the largest dividend and smallest divisor.  An unbounded
    divisor high sends the infimum to 0; an unbounded dividend high sends the
    supremum to +∞.  Stated for arbitrary concrete sets ([IsAlpha]) — hence
    α-complete, not merely best at γ.

    Neither extreme is computed by hand: both are read off [is_glb_of_min] /
    [is_lub_of_max] ([BoundAbstraction.v]) — a value of the image that is below
    (above) every other and is itself in the image is the image's glb (lub).
    Antitonicity in the divisor shows up only as arithmetic, discharged by
    [Z.quot_le_compat_l]; nothing has to be negated and no reversed order has to
    be introduced. *)

(** * The unoptimized quotient chain.

    Each of the nine sign cases is written below as the composition that makes
    its α-completeness immediate: negation transport for the three quarters
    that are not positive/positive, a join of two halves for the across cases.
    That is the whole point of the chain — none of it is extracted.  The
    executable [interval_quot] of [ZIntervalOps.v] computes the same
    intervals in one flat dispatch, and is proved equal to the chain's
    dispatcher [interval_quot_unopt] at the end of this file
    ([interval_quot_unopt_eq]), which is how it inherits [_best]. *)

(** The chain's obligations are [interval_quot]'s, plus "this split half
    has the sign its type claims" for the ±1 halves of a crossing divisor.
    [nz_obligation] ([ZIntervalOps.v]) is written to cover both. *)
#[local] Obligation Tactic := nz_obligation.

(** For positive dividend [l2,h2] and strictly positive divisor [l1,h1]:
  result = [l2/h1, h2/l1]. The two obligations are the divisor's bounds
  being non-zero: the one its type names by its sign, the other because
  [non_bottom] orders the two. *)
Program Definition interval_quot_pos (i2 : interval) (i1 : pos_interval) : interval :=
  let (l2, h2) := i2 in
  let '(l1, h1) := i1 in
  (quot_bound l2 h1 _, quot_bound h2 l1 _).

(** Quarter functions: both dividend and divisor have definite sign. *)

Definition interval_quot_neg_pos (i2 : interval) (i1 : pos_interval) : interval :=
  interval_opp (interval_quot_pos (interval_opp i2) i1).

Program Definition interval_quot_pos_neg (i2 : interval) (i1 : neg_interval) : interval :=
  interval_opp (interval_quot_pos i2 (interval_opp i1)).

Program Definition interval_quot_neg_neg (i2 : interval) (i1 : neg_interval) : interval :=
  interval_quot_pos (interval_opp i2) (interval_opp i1).

(** Across-dividend functions: dividend crosses zero, divisor has definite sign.
    Split the dividend at 0. *)

Definition interval_quot_across_pos (i2 : interval) (i1 : pos_interval) : interval :=
  ZInterval.join
    (interval_quot_neg_pos (fst i2, WithTop.NotTop 0) i1)
    (interval_quot_pos (WithTop.NotTop 0, snd i2) i1).

Definition interval_quot_across_neg (i2 : interval) (i1 : neg_interval) : interval :=
  ZInterval.join
    (interval_quot_neg_neg (fst i2, WithTop.NotTop 0) i1)
    (interval_quot_pos_neg (WithTop.NotTop 0, snd i2) i1).

(** Across-divisor functions: divisor crosses zero.
    Split the divisor into [l1, -1] and [1, h1], excluding 0. The split
    halves are sign-definite by construction, which is what the two
    obligations say. *)

Program Definition interval_quot_pos_across (i2 : interval) (i1 : across_interval)
  : interval :=
  let '(l1, h1) := i1 in
  ZInterval.join
    (interval_quot_pos_neg i2 (l1, WithTop.NotTop (-1)))
    (interval_quot_pos i2 (WithTop.NotTop 1, h1)).

Program Definition interval_quot_neg_across (i2 : interval) (i1 : across_interval)
  : interval :=
  let '(l1, h1) := i1 in
  ZInterval.join
    (interval_quot_neg_neg i2 (l1, WithTop.NotTop (-1)))
    (interval_quot_neg_pos i2 (WithTop.NotTop 1, h1)).

(** Optimized across-divisor functions (moved here so across_across can use them). *)
Definition interval_quot_pos_across_opt (i2 : interval) (i1 : across_interval) : interval :=
  let (_, h2) := i2 in (bound_opp h2, h2).

Definition interval_quot_neg_across_opt (i2 : interval) (i1 : across_interval) : interval :=
  let (l2, _) := i2 in (l2, bound_opp l2).

Definition interval_quot_across_across (i2 : interval) (i1 : across_interval) : interval :=
  let (l2, h2) := i2 in
  ZInterval.join
    (interval_quot_neg_across_opt (l2, WithTop.NotTop 0) i1)
    (interval_quot_pos_across_opt (WithTop.NotTop 0, h2) i1).

Definition interval_quot_unopt (i2 : interval) (i1 : nb_interval) : interval :=
  match classify_divisor i1 with
  | DivZero => ZInterval.bottom
  | DivPos i1_san =>
      match classify i2 with
      | Pos    => interval_quot_pos i2 i1_san
      | Neg    => interval_quot_neg_pos i2 i1_san
      | Across => interval_quot_across_pos i2 i1_san
      end
  | DivNeg i1_san =>
      match classify i2 with
      | Pos    => interval_quot_pos_neg i2 i1_san
      | Neg    => interval_quot_neg_neg i2 i1_san
      | Across => interval_quot_across_neg i2 i1_san
      end
  | DivAcross Hl Hh =>
      let i1_san := exist _ (`i1) (conj Hl Hh) : across_interval in
      match classify i2 with
      | Pos    => interval_quot_pos_across i2 i1_san
      | Neg    => interval_quot_neg_across i2 i1_san
      | Across => interval_quot_across_across i2 i1_san
      end
  end.

(** * [quot_bound] without its proof argument.

    [quot_bound a b Hb] carries a proof that [b] is not [NotTop 0].  That proof
    is what makes extraction to OCaml's raising [Z.div] safe, so it must stay in
    the definition — but no proof below ever looks at it: it is consumed only by
    the transparent [Primitives.quot_non_zero], which drops it.  So
    [quot_bound a b Hb] is convertible to the proof-free [qb a b], whatever
    proof it carries.

    [quot_bound_qb] is the single place in this file that knows [quot_bound]'s
    definition.  Everything downstream rewrites with it first and then reasons
    about [qb] — which is what lets the negation identities below hold with no
    side conditions at all, [Zquot]'s unconditional [Zquot_opp_l] /
    [Zquot_opp_r] / [Zquot_0_l] being true for a zero divisor too.  Rewriting
    also works where [simpl] cannot: on a bound that is still a variable, so the
    [Program] match has nothing to reduce. *)

Local Definition qb (a b : WithTop.with_top Z) : WithTop.with_top Z :=
  match b with
  | WithTop.Top => WithTop.NotTop 0
  | WithTop.NotTop b =>
      match a with
      | WithTop.Top => WithTop.Top
      | WithTop.NotTop a => WithTop.NotTop (a ÷ b)
      end
  end.

Local Lemma quot_bound_qb (a b : WithTop.with_top Z) (Hb : b <> WithTop.NotTop 0) :
  quot_bound a b Hb = qb a b.
Proof.
  by move: Hb; rewrite /quot_bound /qb; case: b; case: a => * //=;
     rewrite Primitives.quot_non_zero_quot.
Qed.

Local Lemma qb_neg_l (a b : WithTop.with_top Z) : qb (bound_opp a) b = bound_opp (qb a b).
Proof. by case: b => [|b]; case: a => [|a] //=; rewrite Zquot.Zquot_opp_l. Qed.

Local Lemma qb_neg_r (a b : WithTop.with_top Z) : qb a (bound_opp b) = bound_opp (qb a b).
Proof. by case: b => [|b]; case: a => [|a] //=; rewrite Zquot.Zquot_opp_r. Qed.

Local Lemma qb_0_l (b : WithTop.with_top Z) : qb (WithTop.NotTop 0) b = WithTop.NotTop 0.
Proof. by case: b => [|b] //=; rewrite Zquot.Zquot_0_l. Qed.

(** Unboundedness of the quotient set: when the dividend set is unbounded
    above and the divisor set has a strictly positive element [d], the
    quotients are unbounded above — a dividend beyond [d * (z + 1)] has a
    quotient beyond [z].  Stated as [IsAlpha] directly rather than through
    [weak_α_relation_spec]: the weak relation asks for the witness
    constructively, whereas [IsAlpha]'s [NotTop] case reduces to [False],
    which is [Stable] and so admits the ¬¬-witness of
    [is_alpha_lubtop_top_nn].  The [Z]-level sibling of
    [MulTheory.IsAlpha_lubtop_top_product_r], used below by
    [interval_quot_pos_alpha_complete]'s [h2 = Top] branch. *)
Lemma IsAlpha_lubtop_top_quot (S2 S1 : ℘ Z) (d : Z) :
  IsAlpha (A:=lubtop) WithTop.Top S2 ->
  0 < d -> d ∈ S1 ->
  IsAlpha (A:=lubtop) WithTop.Top (collecting_quot S2 S1).
Proof.
  move=> Hunb Hd Hdin.
  rewrite /IsAlpha => a; case: a => [|z] /=.
  - by unfold_set; split.
  - unfold_set; split; [|by []].
    move=> Hsub.
    apply: (is_alpha_lubtop_top_nn S2 (d * z + d) Hunb) => [[c2 [Hc2in Hc2gt]]].
    have Hmem : Z.quot c2 d ∈ collecting_quot S2 S1
      by exists c2, d; repeat split; [exact: Hc2in | exact: Hdin | lia].
    have Hle := Hsub _ Hmem; unfold_set in Hle.
    have Hlow : z + 1 <= Z.quot c2 d by apply: Z.quot_le_lower_bound; [lia | nia].
    lia.
Qed.

Lemma interval_quot_pos_alpha_complete
    (l2 : Z) (h2 : WithTop.with_top Z) (i1 : pos_interval) (S2 S1 : ℘ Z) :
  0 <= l2 ->
  (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
  IsAlpha (A:=itv) (WithTop.NotTop l2, h2) S2 ->
  IsAlpha (A:=itv) (`i1) S1 ->
  IsAlpha (A:=itv)
    (interval_quot_pos (WithTop.NotTop l2, h2) i1)
    (collecting_quot S2 S1).
Proof.
  (* A [pos_interval] with a [Top] low bound is refuted by [low_pos]; on
     [NotTop] its payload is exactly [pos_itv]'s, so destructing it puts the
     divisor's bounds and sign facts in the context. *)
  move: i1 => [[[|l1] h1] [Hnb1 Hl1pos]]; first by case: Hl1pos.
  move=> Hl2 Hex2 Hex1 Ha2 Ha1; simpl in Hl1pos, Ha1.
  (* [i1]'s payload is a concrete pair, so the [Program] match in
     [interval_quot_pos] reduces and the conclusion becomes the pair of
     [quot_bound]s. *)
  simpl.
  (* Attained bounds of both operands: the inf/sup witnesses live in S2, S1. *)
  apply: (itv_attained_low_witness (WithTop.NotTop l2) h2 S2 Ha2 Hex2) => Hatl2.
  apply: (itv_attained_high_witness (WithTop.NotTop l2) h2 S2 Ha2 Hex2) => Hath2.
  apply: (itv_attained_low_witness (WithTop.NotTop l1) h1 S1 Ha1 Hex1) => Hatl1.
  apply: (itv_attained_high_witness (WithTop.NotTop l1) h1 S1 Ha1 Hex1) => Hath1.
  have HS2 := gamma_alpha_extensive itv _ _ Ha2.
  have HS1 := gamma_alpha_extensive itv _ _ Ha1.
  move: Ha2 Ha1 => /Conjunction.is_alpha_pair_iff [Hglb2 Hlub2]
                   /Conjunction.is_alpha_pair_iff [Hglb1 Hlub1].
  apply/Conjunction.is_alpha_pair_iff; split.
  + (* GLB = quot_bound l2 h1 : l2 ÷ h1 (0 when h1 = Top). *)
    apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_glbtop)).
    case: h1 HS1 Hnb1 Hlub1 Hath1 => [|h1'] HS1 Hnb1 Hlub1 Hath1 /=.
    * (* h1 = Top: the divisor is unbounded above, so the quotient tends to 0. *)
      rewrite ?quot_bound_qb /=.
      constructor.
      -- move=> z [c2 [c1 [Hc2 [Hc1 [Hne Hz]]]]]; subst z.
         have /gamma_itv_low Hlo2 := HS2 _ Hc2.
         have /gamma_itv_low Hlo1 := HS1 _ Hc1.
         apply Z.quot_pos; lia.
      -- (* 0 is the *greatest* lower bound: 0 is realized as [l2 ÷ c1] for
            any divisor [c1 > l2], and the divisor set has one since it is
            unbounded above.  Deciding [z <= 0] first leaves [False] as the
            goal, which is [Stable] and so admits that ¬¬-witness. *)
         move=> z Hz. case: (Z.le_gt_cases z 0) => [//|Hzpos]; exfalso.
         apply: (is_alpha_lubtop_top_witness S1 (Z.max l2 0) Hlub1) => [[c1 [Hc1 Hc1gt]]].
         have H0 : 0 ∈ collecting_quot S2 S1.
         { exists l2, c1; unfold_set.
           have -> : Z.quot l2 c1 = 0 by apply Z.quot_small; lia.
           repeat split; [exact: Hatl2 | exact: Hc1 | lia]. }
         have := Hz 0 H0; lia.
    * (* h1 = NotTop h1': the infimum is attained at (smallest dividend,
         largest divisor), so it is a *member* of the quotient set and below all
         of it — which is [is_glb_of_min]. *)
      rewrite ?quot_bound_qb /=.
      simpl in Hnb1.
      apply: is_glb_of_min;
        first by exists l2, h1'; unfold_set; repeat split => //; lia.
      (* [l2 ÷ h1' <= l2 ÷ c1 <= c2 ÷ c1]: antitone in the divisor, then
         monotone in the dividend.  Both operands' bounds are read off their γ,
         which also gives the divisor's positivity. *)
      move=> z; unfold_set; move=> [c2 [c1 [Hc2 [Hc1 [_ <-]]]]].
      have /gamma_itv_low Hlo2 := HS2 _ Hc2.
      have /gamma_itv_low Hlo1 := HS1 _ Hc1.
      have /gamma_itv_high Hhi1 := HS1 _ Hc1.
      transitivity (l2 ÷ c1);
        first [apply Z.quot_le_compat_l | apply Z.quot_le_mono]; lia.
  + (* LUB = quot_bound h2 l1 : h2 ÷ l1 (Top when h2 = Top). *)
    case: h2 HS2 Hath2 Hlub2 => [|h2'] HS2 Hath2 Hlub2 /=.
    * (* h2 = Top: the dividend is unbounded above, and the divisor has the
          positive element l1, so the quotient is unbounded above. *)
      rewrite ?quot_bound_qb /=.
      exact: (IsAlpha_lubtop_top_quot S2 S1 l1 Hlub2 Hl1pos Hatl1).
    * (* h2 = NotTop h2': mirror — the supremum is attained at (largest
         dividend, smallest divisor). *)
      apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_lubtop)).
      rewrite ?quot_bound_qb /=.
      apply: is_lub_of_max; first by exists h2', l1; unfold_set; repeat split=> //; lia.
      (* [c2 ÷ c1 <= c2 ÷ l1 <= h2' ÷ l1]. *)
      move=> z; unfold_set; move=> [c2 [c1 [Hc2 [Hc1 [_ <-]]]]].
      have /gamma_itv_low Hlo2 := HS2 _ Hc2.
      have /gamma_itv_high Hhi2 := HS2 _ Hc2.
      have /gamma_itv_low Hlo1 := HS1 _ Hc1.
      transitivity (c2 ÷ l1);
        first [apply Z.quot_le_compat_l | apply Z.quot_le_mono]; lia.
Qed.

(** * The three other quarters, by negation transport.

    Each reduces to [interval_quot_pos_alpha_complete] through
    [is_alpha_opp_iff] and the [collecting_quot_opp_*] commutations: negate
    the operand(s) of the wrong sign, apply the quarter, and negate the
    result back.  The abstract side needs no rewriting — the quotient chain
    defines each case as exactly that composition of [interval_opp]s. *)

Lemma interval_quot_neg_pos_alpha_complete
    (l2 : WithTop.with_top Z) (h2 : Z) (i1 : pos_interval) (S2 S1 : ℘ Z) :
  h2 <= 0 ->
  (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
  IsAlpha (A:=itv) (l2, WithTop.NotTop h2) S2 ->
  IsAlpha (A:=itv) (`i1) S1 ->
  IsAlpha (A:=itv)
    (interval_quot_neg_pos (l2, WithTop.NotTop h2) i1)
    (collecting_quot S2 S1).
Proof.
  move=> Hh2 Hex2 Hex1 Ha2 Ha1.
  have Hpos := interval_quot_pos_alpha_complete (-h2) (bound_opp l2) i1
                 {[ z | -z ∈ S2 ]} S1 ltac:(lia) (opp_nonempty _ Hex2) Hex1
                 ((is_alpha_opp_iff _ _).1 Ha2) Ha1.
  exact: (is_alpha_set_equiv _ _ _
            (propset_opp_equiv_inv _ _ (collecting_quot_opp_l S2 S1))
            ((is_alpha_opp_iff _ _).1 Hpos)).
Qed.

Lemma interval_quot_pos_neg_alpha_complete
    (l2 : Z) (h2 : WithTop.with_top Z) (i1 : neg_interval) (S2 S1 : ℘ Z) :
  0 <= l2 ->
  (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
  IsAlpha (A:=itv) (WithTop.NotTop l2, h2) S2 ->
  IsAlpha (A:=itv) (`i1) S1 ->
  IsAlpha (A:=itv)
    (interval_quot_pos_neg (WithTop.NotTop l2, h2) i1)
    (collecting_quot S2 S1).
Proof.
  move=> Hl2 Hex2 Hex1 Ha2 Ha1.
  have Hpos := interval_quot_pos_alpha_complete l2 h2 (opp_neg_pos i1)
                 S2 {[ z | -z ∈ S1 ]} Hl2 Hex2 (opp_nonempty _ Hex1)
                 Ha2 ((is_alpha_opp_iff _ _).1 Ha1).
  exact: (is_alpha_set_equiv _ _ _
            (propset_opp_equiv_inv _ _ (collecting_quot_opp_r S2 S1))
            ((is_alpha_opp_iff _ _).1 Hpos)).
Qed.

Lemma interval_quot_neg_neg_alpha_complete
    (l2 : WithTop.with_top Z) (h2 : Z) (i1 : neg_interval) (S2 S1 : ℘ Z) :
  h2 <= 0 ->
  (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
  IsAlpha (A:=itv) (l2, WithTop.NotTop h2) S2 ->
  IsAlpha (A:=itv) (`i1) S1 ->
  IsAlpha (A:=itv)
    (interval_quot_neg_neg (l2, WithTop.NotTop h2) i1)
    (collecting_quot S2 S1).
Proof.
  move=> Hh2 Hex2 Hex1 Ha2 Ha1.
  have Hpos := interval_quot_pos_alpha_complete (-h2) (bound_opp l2) (opp_neg_pos i1)
                 {[ z | -z ∈ S2 ]} {[ z | -z ∈ S1 ]}
                 ltac:(lia) (opp_nonempty _ Hex2) (opp_nonempty _ Hex1)
                 ((is_alpha_opp_iff _ _).1 Ha2) ((is_alpha_opp_iff _ _).1 Ha1).
  exact: (is_alpha_set_equiv _ _ _ (collecting_quot_opp_both S2 S1) Hpos).
Qed.

(** * The across cases, by splitting and joining.

    A crossing operand is cut in two sign-definite halves, each abstracted by
    the matching quarter, and the results joined ([is_alpha_join_split]).  The
    two operands behave very differently under that cut, and that is what
    decides whether a case is named [_alpha_complete] or [_best].

    A crossing *dividend* costs nothing.  The cut is
    [collecting_quot_split_dividend], the two halves are abstracted at their
    own bounds by [itv_split_at_zero_alpha], and the transfer function's fixed
    cut at 0 is recovered by the absorption lemmas below.  Both operand sets
    stay arbitrary, so these cases are genuinely α-complete.

    A crossing *divisor* is stated at a concretization instead, because the
    extremal nonzero divisors have to be named and only γ pins them to ∓1
    ([gamma_itv_neg_half] / [gamma_itv_pos_half]).  That is not an artefact of
    the proof: α-completeness is provably false in that case — see
    [quot_across_no_alpha_complete] at the end of this file, which is why those
    lemmas are named [_best] and cannot be strengthened.  A half is then the
    best abstraction of its own γ ([non_bottom_is_alpha_gamma]), which is what
    feeds the quarter lemma. *)

(** Reduce a quotient-chain interval to arithmetic: unfold the join and the
    negation, then divide by the ±1 bounds.

    This is the counterpart of [qb_norm] for goals whose bounds have already
    been split into constructors: there [simpl] reduces [quot_bound] on its own,
    stopping at [quot_non_zero] (which is [simpl never], so that the non-zero
    obligation cannot be stepped past by accident), and
    [Primitives.quot_non_zero_quot] takes the last step explicitly.  Where the
    bounds are still variables [simpl] can do nothing and [quot_bound_qb] is the
    only way through. *)
Local Ltac quot_join_compute :=
  rewrite /ZInterval.join /Conjunction.join
          /ZInterval.join_lb /ZInterval.join_ub /interval_opp /bound_opp /=;
  rewrite ?Primitives.quot_non_zero_quot ?Z.quot_1_r //.

(** The sign counterpart of [Z.quot_pos], which the standard library does not
    provide: truncation towards zero is odd, so a non-positive dividend over a
    positive divisor gives a non-positive quotient. *)
Local Lemma quot_nonpos (a b : Z) : a <= 0 -> 0 < b -> a ÷ b <= 0.
Proof.
  move=> Ha Hb.
  have Hb0 : b <> 0 by lia.
  have H := Z.quot_pos (-a) b ltac:(lia) ltac:(lia).
  rewrite (Z.quot_opp_l a b Hb0) in H. lia.
Qed.

(** The same two, for a negative divisor: truncation is odd in the divisor
    too, so each sign flips. *)
Local Lemma quot_neg_nonneg (a b : Z) : a <= 0 -> b < 0 -> 0 <= a ÷ b.
Proof.
  move=> Ha Hb; have H := quot_nonpos a (-b) Ha ltac:(lia).
  by rewrite -(Z.opp_involutive b) Zquot.Zquot_opp_r; lia.
Qed.

Local Lemma quot_neg_nonpos (a b : Z) : 0 <= a -> b < 0 -> a ÷ b <= 0.
Proof.
  move=> Ha Hb; have H := Z.quot_pos a (-b) Ha ltac:(lia).
  by rewrite -(Z.opp_involutive b) Zquot.Zquot_opp_r; lia.
Qed.

(** Give [lia] the sign of every quotient appearing in the goal, so that it can
    settle the [Z.min] / [Z.max] of the join.  The guard keeps [repeat] from
    looping on a quotient whose sign is already known. *)
Local Ltac quot_signs :=
  repeat match goal with
  | |- context [ Z.quot ?a ?b ] =>
      lazymatch goal with
      | _ : 0 <= Z.quot a b |- _ => fail
      | _ : Z.quot a b <= 0 |- _ => fail
      | _ => first [ pose proof (Z.quot_pos a b ltac:(simpl in *; lia)
                                                ltac:(simpl in *; lia))
                   | pose proof (quot_nonpos a b ltac:(simpl in *; lia)
                                                ltac:(simpl in *; lia))
                   | pose proof (quot_neg_nonneg a b ltac:(simpl in *; lia)
                                                   ltac:(simpl in *; lia))
                   | pose proof (quot_neg_nonpos a b ltac:(simpl in *; lia)
                                                   ltac:(simpl in *; lia)) ]
      end
  end.

(** * Where the dividend is cut does not matter.

    The two halves of a crossing dividend are abstracted at their own bounds —
    [(l2, m)] with [m <= 0] and [(p, h2)] with [0 <= p] — but the transfer
    function cuts at [0].  The difference is confined to the two *inner* ends of
    the join, and with a sign-definite divisor those sit on the wrong side of
    [0] to survive it: one half's quotients are all non-positive, the other's
    all non-negative, so the join keeps the two *outer* ends whatever [m] and
    [p] are.

    This is what makes the across-dividend cases α-complete rather than merely
    best at γ: the abstract value does not depend on the split point, so it need
    not know it.  (The across-*divisor* cases have no such collapse, and are
    provably not α-complete — see [quot_across_no_alpha_complete] at the end of
    this file.) *)

Local Lemma interval_quot_across_pos_join_eq
    (l2 h2 : WithTop.with_top Z) (m p : Z) (i1 : pos_interval) :
  0 ∈ γ[glbtop] l2 -> 0 ∈ γ[lubtop] h2 -> m <= 0 -> 0 <= p ->
  ZInterval.join (interval_quot_neg_pos (l2, WithTop.NotTop m) i1)
                 (interval_quot_pos (WithTop.NotTop p, h2) i1)
  = interval_quot_across_pos (l2, h2) i1.
Proof.
  move: i1 => [[[|l1] h1] [Hnb Hl1]]; first by case: Hl1.
  simpl in Hnb, Hl1.
  move: Hnb; case: h1 => [|h1]; case: l2 => [|l2]; case: h2 => [|h2]
    => Hnb Hl2 Hh2 Hm Hp;
    unfold_set in Hl2; unfold_set in Hh2; simpl in Hl2, Hh2, Hnb;
    rewrite /interval_quot_across_pos /interval_quot_neg_pos /interval_quot_pos /=;
    quot_join_compute.
  all: f_equal; f_equal; quot_signs; lia.
Qed.

(** Mirror, for a strictly negative divisor: the two halves swap roles (a
    non-positive dividend over a negative divisor is non-negative), but the
    inner ends are absorbed just the same. *)
Local Lemma interval_quot_across_neg_join_eq
    (l2 h2 : WithTop.with_top Z) (m p : Z) (i1 : neg_interval) :
  0 ∈ γ[glbtop] l2 -> 0 ∈ γ[lubtop] h2 -> m <= 0 -> 0 <= p ->
  ZInterval.join (interval_quot_neg_neg (l2, WithTop.NotTop m) i1)
                 (interval_quot_pos_neg (WithTop.NotTop p, h2) i1)
  = interval_quot_across_neg (l2, h2) i1.
Proof.
  move: i1 => [[l1 [|h1]] [Hnb Hh1]]; first by case: Hh1.
  simpl in Hnb, Hh1.
  move: Hnb; case: l1 => [|l1]; case: l2 => [|l2]; case: h2 => [|h2]
    => Hnb Hl2 Hh2 Hm Hp;
    unfold_set in Hl2; unfold_set in Hh2; simpl in Hl2, Hh2, Hnb;
    rewrite /interval_quot_across_neg /interval_quot_neg_neg /interval_quot_pos_neg
            /interval_quot_pos /=;
    quot_join_compute.
  all: f_equal; f_equal; quot_signs; lia.
Qed.

(** Dividend crossing 0, divisor strictly positive: split the dividend at 0
    into a negative and a positive half. *)
Lemma interval_quot_across_pos_alpha_complete
    (l2 h2 : WithTop.with_top Z) (i1 : pos_interval) (S2 S1 : ℘ Z) :
  0 ∈ γ[glbtop] l2 -> 0 ∈ γ[lubtop] h2 ->
  (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
  IsAlpha (A:=itv) (l2, h2) S2 ->
  IsAlpha (A:=itv) (`i1) S1 ->
  IsAlpha (A:=itv)
    (interval_quot_across_pos (l2, h2) i1)
    (collecting_quot S2 S1).
Proof.
  move=> Hl2 Hh2 Hex2 Hex1 Ha2 Ha1.
  move: (Ha2) => /Conjunction.is_alpha_pair_iff [Hglb2 Hlub2].
  (* The halves are abstracted at their own bounds [m], [p]; the transfer
     function's cut at 0 is recovered by [interval_quot_across_pos_join_eq]. *)
  apply: (itv_split_at_zero_alpha l2 h2 S2 Hl2 Hh2 Hex2 Ha2)
    => m p Hm Hp Han Hap HmS HpS.
  have Hmemn : m ∈ {[ z | z ∈ S2 /\ z <= 0 ]} by unfold_set; split.
  have Hmemp : p ∈ {[ z | z ∈ S2 /\ 0 <= z ]} by unfold_set; split.
  have Hn := interval_quot_neg_pos_alpha_complete l2 m i1
                {[ z | z ∈ S2 /\ z <= 0 ]} S1 Hm (nonempty_of_mem _ _ Hmemn) Hex1 Han Ha1.
  have Hp' := interval_quot_pos_alpha_complete p h2 i1
                 {[ z | z ∈ S2 /\ 0 <= z ]} S1 Hp (nonempty_of_mem _ _ Hmemp) Hex1 Hap Ha1.
  rewrite -(interval_quot_across_pos_join_eq l2 h2 m p i1 Hl2 Hh2 Hm Hp).
  apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp').
  exact: (collecting_quot_split_dividend S2 S1).
Qed.

(** Mirror: dividend crossing 0, divisor strictly negative. *)
Lemma interval_quot_across_neg_alpha_complete
    (l2 h2 : WithTop.with_top Z) (i1 : neg_interval) (S2 S1 : ℘ Z) :
  0 ∈ γ[glbtop] l2 -> 0 ∈ γ[lubtop] h2 ->
  (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
  IsAlpha (A:=itv) (l2, h2) S2 ->
  IsAlpha (A:=itv) (`i1) S1 ->
  IsAlpha (A:=itv)
    (interval_quot_across_neg (l2, h2) i1)
    (collecting_quot S2 S1).
Proof.
  move=> Hl2 Hh2 Hex2 Hex1 Ha2 Ha1.
  apply: (itv_split_at_zero_alpha l2 h2 S2 Hl2 Hh2 Hex2 Ha2)
    => m p Hm Hp Han Hap HmS HpS.
  have Hmemn : m ∈ {[ z | z ∈ S2 /\ z <= 0 ]} by unfold_set; split.
  have Hmemp : p ∈ {[ z | z ∈ S2 /\ 0 <= z ]} by unfold_set; split.
  have Hn := interval_quot_neg_neg_alpha_complete l2 m i1
               {[ z | z ∈ S2 /\ z <= 0 ]} S1 Hm (nonempty_of_mem _ _ Hmemn) Hex1 Han Ha1.
  have Hp' := interval_quot_pos_neg_alpha_complete p h2 i1
                {[ z | z ∈ S2 /\ 0 <= z ]} S1 Hp (nonempty_of_mem _ _ Hmemp) Hex1 Hap Ha1.
  rewrite -(interval_quot_across_neg_join_eq l2 h2 m p i1 Hl2 Hh2 Hm Hp).
  apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp').
  exact: (collecting_quot_split_dividend S2 S1).
Qed.

(** * The across-divisor cases, α-complete relative to a supplied split.

    [quot_across_no_alpha_complete] (end of this file) shows there is no
    α-complete transfer function of the two *intervals* here: the quotient's
    extremes sit at the divisor values nearest zero, and an interval cannot say
    which those are.  What *is* α-complete is the join taken at the two halves'
    own bounds, [m] and [p] — and the point of the lemmas below is that they
    take that split as a **hypothesis** rather than computing it.

    That is what makes them the entry point for a richer domain.  To prove
    bestness of the quotient on interval×congruence (or interval×known-bits),
    the caller:

    - computes [m], the largest negative divisor, and [p], the smallest
      positive one — for a congruence [z ≡ a mod n] these are exact and cheap,
      where an interval could only say [m <= -1 <= 1 <= p];
    - discharges [IsAlpha (l1, NotTop m)] and [IsAlpha (NotTop p, h1)] on the
      two halves of its own concrete set, which is where the congruence
      information is spent;
    - reads off the interval component of the product's best abstraction.

    Nothing else about the operand sets is assumed, and nothing here needs
    [Stable] or a continuation: the split is data the caller has.  The
    interval-only instance, which has to *derive* the split, is the
    [_abstract] corollary below. *)

Lemma interval_quot_pos_across_split_alpha_complete
    (l2 : Z) (h2 l1 h1 : WithTop.with_top Z) (m p : Z)
    (Hm : m < 0) (Hp : 0 < p)
    (Hnbn : non_bottom (l1, WithTop.NotTop m))
    (Hnbp : non_bottom (WithTop.NotTop p, h1))
    (S2 S1 : ℘ Z) :
  0 <= l2 ->
  (exists c, c ∈ S2) ->
  m ∈ S1 -> p ∈ S1 ->
  IsAlpha (A:=itv) (WithTop.NotTop l2, h2) S2 ->
  IsAlpha (A:=itv) (l1, WithTop.NotTop m) {[ z | z ∈ S1 /\ z < 0 ]} ->
  IsAlpha (A:=itv) (WithTop.NotTop p, h1) {[ z | z ∈ S1 /\ 0 < z ]} ->
  IsAlpha (A:=itv)
    (ZInterval.join
       (interval_quot_pos_neg (WithTop.NotTop l2, h2) (neg_itv l1 m Hm Hnbn))
       (interval_quot_pos (WithTop.NotTop l2, h2) (pos_itv p h1 Hp Hnbp)))
    (collecting_quot S2 S1).
Proof.
  move=> Hl2 Hex2 HmS HpS Ha2 Han Hap.
  have Hexn : exists c, c ∈ {[ z | z ∈ S1 /\ z < 0 ]} by exists m; unfold_set; split.
  have Hexp : exists c, c ∈ {[ z | z ∈ S1 /\ 0 < z ]} by exists p; unfold_set; split.
  have Hn := interval_quot_pos_neg_alpha_complete l2 h2 (neg_itv l1 m Hm Hnbn)
               S2 {[ z | z ∈ S1 /\ z < 0 ]} Hl2 Hex2 Hexn Ha2 Han.
  have Hp' := interval_quot_pos_alpha_complete l2 h2 (pos_itv p h1 Hp Hnbp)
                S2 {[ z | z ∈ S1 /\ 0 < z ]} Hl2 Hex2 Hexp Ha2 Hap.
  apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp').
  exact: (collecting_quot_split_divisor_set S2 S1).
Qed.

(** Mirror, for a non-positive dividend. *)
Lemma interval_quot_neg_across_split_alpha_complete
    (l2 : WithTop.with_top Z) (h2 : Z) (l1 h1 : WithTop.with_top Z) (m p : Z)
    (Hm : m < 0) (Hp : 0 < p)
    (Hnbn : non_bottom (l1, WithTop.NotTop m))
    (Hnbp : non_bottom (WithTop.NotTop p, h1))
    (S2 S1 : ℘ Z) :
  h2 <= 0 ->
  (exists c, c ∈ S2) ->
  m ∈ S1 -> p ∈ S1 ->
  IsAlpha (A:=itv) (l2, WithTop.NotTop h2) S2 ->
  IsAlpha (A:=itv) (l1, WithTop.NotTop m) {[ z | z ∈ S1 /\ z < 0 ]} ->
  IsAlpha (A:=itv) (WithTop.NotTop p, h1) {[ z | z ∈ S1 /\ 0 < z ]} ->
  IsAlpha (A:=itv)
    (ZInterval.join
       (interval_quot_neg_neg (l2, WithTop.NotTop h2) (neg_itv l1 m Hm Hnbn))
       (interval_quot_neg_pos (l2, WithTop.NotTop h2) (pos_itv p h1 Hp Hnbp)))
    (collecting_quot S2 S1).
Proof.
  move=> Hh2 Hex2 HmS HpS Ha2 Han Hap.
  have Hexn : exists c, c ∈ {[ z | z ∈ S1 /\ z < 0 ]} by exists m; unfold_set; split.
  have Hexp : exists c, c ∈ {[ z | z ∈ S1 /\ 0 < z ]} by exists p; unfold_set; split.
  have Hn := interval_quot_neg_neg_alpha_complete l2 h2 (neg_itv l1 m Hm Hnbn)
               S2 {[ z | z ∈ S1 /\ z < 0 ]} Hh2 Hex2 Hexn Ha2 Han.
  have Hp' := interval_quot_neg_pos_alpha_complete l2 h2 (pos_itv p h1 Hp Hnbp)
                S2 {[ z | z ∈ S1 /\ 0 < z ]} Hh2 Hex2 Hexp Ha2 Hap.
  apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp').
  exact: (collecting_quot_split_divisor_set S2 S1).
Qed.

(** Divisor crossing 0, dividend non-negative: split the divisor at ±1.  The
    two halves are the sign-definite divisors the chain builds; their
    [pos_interval] / [neg_interval] payloads come from the goal, so the sign
    facts never have to be rebuilt here — [across_interval] carries them. *)
Lemma interval_quot_pos_across_best
    (l2 : Z) (h2 : WithTop.with_top Z) (i1 : across_interval) (S2 : ℘ Z) :
  0 <= l2 -> (exists c, c ∈ S2) ->
  IsAlpha (A:=itv) (WithTop.NotTop l2, h2) S2 ->
  IsAlpha (A:=itv)
    (interval_quot_pos_across (WithTop.NotTop l2, h2) i1)
    (collecting_quot S2 (γ[itv] (`i1))).
Proof.
  move: i1 => [[l1 h1] [Hl1 Hh1]] Hl2 Hex2 Ha2; simpl in Hl1, Hh1.
  have [Hm1 [Hnbn Hnm]] := across_neg_half_alpha l1 h1 Hl1 Hh1.
  have [Hp1 [Hnbp Hpm]] := across_pos_half_alpha l1 h1 Hl1 Hh1.
  apply: interval_quot_pos_across_split_alpha_complete; first [assumption | lia].
Qed.

(** Mirror: divisor crossing 0, dividend non-positive. *)
Lemma interval_quot_neg_across_best
    (l2 : WithTop.with_top Z) (h2 : Z) (i1 : across_interval) (S2 : ℘ Z) :
  h2 <= 0 -> (exists c, c ∈ S2) ->
  IsAlpha (A:=itv) (l2, WithTop.NotTop h2) S2 ->
  IsAlpha (A:=itv)
    (interval_quot_neg_across (l2, WithTop.NotTop h2) i1)
    (collecting_quot S2 (γ[itv] (`i1))).
Proof.
  move: i1 => [[l1 h1] [Hl1 Hh1]] Hh2 Hex2 Ha2; simpl in Hl1, Hh1.
  have [Hm1 [Hnbn Hnm]] := across_neg_half_alpha l1 h1 Hl1 Hh1.
  have [Hp1 [Hnbp Hpm]] := across_pos_half_alpha l1 h1 Hl1 Hh1.
  apply: interval_quot_neg_across_split_alpha_complete; first [assumption | lia].
Qed.


(** * The optimized across-divisor forms.

    A non-negative dividend divided by a divisor of absolute value at least 1
    stays within [[-h2, h2]], and both ends are attained (divide the top of
    the dividend by ±1), so the join of the two divisor halves collapses to
    [(-h2, h2)] — which is what [interval_quot_pos_across_opt] returns without
    dividing at all.  Proved as an equality of abstract values, so the
    α-completeness of the general form transports verbatim. *)
Lemma interval_quot_pos_across_opt_eq
    (l2 : Z) (h2 : WithTop.with_top Z) (i1 : across_interval) :
  0 <= l2 -> non_bottom (WithTop.NotTop l2, h2) ->
  interval_quot_pos_across_opt (WithTop.NotTop l2, h2) i1
  = interval_quot_pos_across (WithTop.NotTop l2, h2) i1.
Proof.
  move: i1 => [[l1 h1] [Hl1 Hh1]]; simpl in Hl1, Hh1.
  move: Hl1 Hh1; case: l1 => [|l1]; case: h1 => [|h1]; case: h2 => [|h2] Hl1 Hh1 Hl2 Hnb;
    rewrite /interval_quot_pos_across_opt /interval_quot_pos_across
            /interval_quot_pos_neg /interval_quot_pos /=;
    quot_join_compute.
  (* The four finite-[h2] goals: each end of the join is the one the ±1
     divisor contributes. *)
  all: simpl in Hnb; f_equal; f_equal;
       first [ rewrite Z.min_l | rewrite Z.max_r ]; try lia.
  all: quot_signs; lia.
Qed.

(** Mirror, for a non-positive dividend: the collapse is to [(l2, -l2)]. *)
Lemma interval_quot_neg_across_opt_eq
    (l2 : WithTop.with_top Z) (h2 : Z) (i1 : across_interval) :
  h2 <= 0 -> non_bottom (l2, WithTop.NotTop h2) ->
  interval_quot_neg_across_opt (l2, WithTop.NotTop h2) i1
  = interval_quot_neg_across (l2, WithTop.NotTop h2) i1.
Proof.
  move: i1 => [[l1 h1] [Hl1 Hh1]]; simpl in Hl1, Hh1.
  move: Hl1 Hh1; case: l1 => [|l1]; case: h1 => [|h1]; case: l2 => [|l2] Hl1 Hh1 Hh2 Hnb;
    rewrite /interval_quot_neg_across_opt /interval_quot_neg_across
            /interval_quot_neg_neg /interval_quot_neg_pos
            /interval_quot_pos /=;
    quot_join_compute.
  all: simpl in Hnb; f_equal; f_equal;
       first [ rewrite Z.min_r | rewrite Z.max_l ]; try lia.
  all: quot_signs; lia.
Qed.

Definition classified_interval {i : interval} (c : divisor_classification i) : interval :=
  match c with
  | DivPos p => `p
  | DivNeg n => `n
  | DivZero => ZInterval.bottom
  | DivAcross _ _ => i
  end.

Local Ltac zcases :=
  repeat (repeat (case: (Z_lt_dec _ _) => ? || case: (Z.eq_dec _ _) => ?);
          simpl in *; try discriminate; try lia).

Lemma classify_divisor_quot_equiv (i : nb_interval) (S2 : ℘ Z) :
  collecting_quot S2 (γ[itv] (classified_interval (classify_divisor i)))
  ⊆⊇ collecting_quot S2 (γ[itv] (`i)).
Proof.
  move: i => [[[|l] [|h]] Hnb]; rewrite /classify_divisor /classified_interval /=; zcases.
  (* [DivAcross] returns its argument untouched; every other leaf drops
     exactly [0], which [collecting_quot] excludes anyway. *)
  all: first [ reflexivity
             | apply: collecting_quot_restrict_equiv;
               unfold_set_equiv => z; unfold_set; simpl in *; intuition lia ].
Qed.

(** α-completeness of the optimized forms is the general one transported
    across the equality. *)
Lemma interval_quot_pos_across_opt_best
    (l2 : Z) (h2 : WithTop.with_top Z) (i1 : across_interval) (S2 : ℘ Z) :
  0 <= l2 -> (exists c, c ∈ S2) ->
  IsAlpha (A:=itv) (WithTop.NotTop l2, h2) S2 ->
  IsAlpha (A:=itv)
    (interval_quot_pos_across_opt (WithTop.NotTop l2, h2) i1)
    (collecting_quot S2 (γ[itv] (`i1))).
Proof.
  move=> Hl2 Hex2 Ha2.
  have [w Hw] := Hex2.
  have Hnb := non_bottom_of_alpha _ _ _ Ha2 Hw.
  rewrite (interval_quot_pos_across_opt_eq l2 h2 i1 Hl2 Hnb).
  apply: (interval_quot_pos_across_best l2 h2 i1 S2); assumption.
Qed.

Lemma interval_quot_neg_across_opt_best
    (l2 : WithTop.with_top Z) (h2 : Z) (i1 : across_interval) (S2 : ℘ Z) :
  h2 <= 0 -> (exists c, c ∈ S2) ->
  IsAlpha (A:=itv) (l2, WithTop.NotTop h2) S2 ->
  IsAlpha (A:=itv)
    (interval_quot_neg_across_opt (l2, WithTop.NotTop h2) i1)
    (collecting_quot S2 (γ[itv] (`i1))).
Proof.
  move=> Hh2 Hex2 Ha2.
  have [w Hw] := Hex2.
  have Hnb := non_bottom_of_alpha _ _ _ Ha2 Hw.
  rewrite (interval_quot_neg_across_opt_eq l2 h2 i1 Hh2 Hnb).
  apply: (interval_quot_neg_across_best l2 h2 i1 S2); assumption.
Qed.

(** Both operands crossing 0: split the dividend at 0 and let each half meet
    the whole across divisor through its optimized form. *)
Lemma interval_quot_across_across_best
    (l2 h2 : WithTop.with_top Z) (i1 : across_interval) (S2 : ℘ Z) :
  0 ∈ γ[glbtop] l2 -> 0 ∈ γ[lubtop] h2 ->
  (exists c, c ∈ S2) ->
  IsAlpha (A:=itv) (l2, h2) S2 ->
  IsAlpha (A:=itv)
    (interval_quot_across_across (l2, h2) i1)
    (collecting_quot S2 (γ[itv] (`i1))).
Proof.
  move=> Hl2 Hh2 Hex2 Ha2.
  apply: (itv_split_at_zero_alpha l2 h2 S2 Hl2 Hh2 Hex2 Ha2)
    => m p Hm Hp Han Hap HmS HpS.
  have Hmemn : m ∈ {[ z | z ∈ S2 /\ z <= 0 ]} by unfold_set; split.
  have Hmemp : p ∈ {[ z | z ∈ S2 /\ 0 <= z ]} by unfold_set; split.
  have Hn := interval_quot_neg_across_opt_best l2 m i1
               {[ z | z ∈ S2 /\ z <= 0 ]} Hm (nonempty_of_mem _ _ Hmemn) Han.
  have Hp' := interval_quot_pos_across_opt_best p h2 i1
                {[ z | z ∈ S2 /\ 0 <= z ]} Hp (nonempty_of_mem _ _ Hmemp) Hap.
  (* No join equality is needed here: the optimized forms read only the *outer*
     bound of their operand, so neither half's abstract value mentions [m] or
     [p], and the join is convertible to the transfer function's. *)
  apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp').
  exact: (collecting_quot_split_dividend S2 (γ[itv] (`i1))).
Qed.

(** * The dispatcher.

    [interval_quot_unopt] classifies the divisor, then the dividend, and calls
    the matching case above.  Each branch is the α-completeness lemma of that
    case at γ; [classify_divisor_quot_equiv] has already replaced the divisor
    by its sanitized payload, and the payload's own type supplies the sign.
    Specializing α-completeness to concretizations is what turns it into
    [BestAbstraction] ([is_alpha_iff_best_abstraction]). *)
Lemma interval_quot_unopt_best (i2 : interval) (i1 : nb_interval) :
  non_bottom i2 ->
  classify_divisor i1 <> DivZero ->
  BestAbstraction (A:=itv) (interval_quot_unopt i2 i1)
    (collecting_quot (γ[itv] i2) (γ[itv] (`i1))).
Proof.
  move=> Hnb2 HnZ.
  have /non_bottom_non_empty Hex2 := Hnb2.
  have Ha2 := non_bottom_is_alpha_gamma _ Hnb2.
  apply/is_alpha_iff_best_abstraction.
  apply: (is_alpha_set_equiv _ _ _ (classify_divisor_quot_equiv i1 (γ[itv] i2))).
  rewrite /interval_quot_unopt.
  move: i2 Hnb2 Hex2 Ha2 => [l2 h2] Hnb2 Hex2 Ha2.
  case Hcd: (classify_divisor i1) => [iP | iN | | Hl Hh].
  - (* DivPos: the payload is a strictly positive divisor. *)
    have Hd : non_bottom (`iP) by case: iP {Hcd} => [? [? ?]].
    have /non_bottom_non_empty Hexd := Hd.
    have Had := non_bottom_is_alpha_gamma _ Hd.
    case Hc2: (classify (l2, h2)).
    + move: (classify_Pos_inv _ _ Hc2) => [l2' [Heq Hl2']]; subst.
      apply: (interval_quot_pos_alpha_complete l2' h2 iP _ _); assumption.
    + move: (classify_Neg_inv _ _ Hc2) => [h2' [Heq Hh2']]; subst.
      apply: (interval_quot_neg_pos_alpha_complete l2 h2' iP _ _); assumption.
    + move: (classify_Across_inv _ _ Hnb2 Hc2) => [Hl2z Hh2z].
      apply: (interval_quot_across_pos_alpha_complete l2 h2 iP _ _); assumption.
  - (* DivNeg: the payload is a strictly negative divisor. *)
    have Hd : non_bottom (`iN) by case: iN {Hcd} => [? [? ?]].
    have /non_bottom_non_empty Hexd := Hd.
    have Had := non_bottom_is_alpha_gamma _ Hd.
    case Hc2: (classify (l2, h2)).
    + move: (classify_Pos_inv _ _ Hc2) => [l2' [Heq Hl2']]; subst.
      apply: (interval_quot_pos_neg_alpha_complete l2' h2 iN _ _); assumption.
    + move: (classify_Neg_inv _ _ Hc2) => [h2' [Heq Hh2']]; subst.
      apply: (interval_quot_neg_neg_alpha_complete l2 h2' iN _ _); assumption.
    + move: (classify_Across_inv _ _ Hnb2 Hc2) => [Hl2z Hh2z].
      apply: (interval_quot_across_neg_alpha_complete l2 h2 iN _ _); assumption.
  - (* DivZero: excluded by hypothesis. *)
    by rewrite Hcd in HnZ.
  - (* DivAcross: the divisor is its own payload. *)
    have Hd : non_bottom (`i1) := across_non_bottom _ Hl Hh.
    have /non_bottom_non_empty Hexd := Hd.
    case Hc2: (classify (l2, h2)).
    + move: (classify_Pos_inv _ _ Hc2) => [l2' [Heq Hl2']]; subst.
      apply: (interval_quot_pos_across_best l2' h2 _ _); assumption.
    + move: (classify_Neg_inv _ _ Hc2) => [h2' [Heq Hh2']]; subst.
      apply: (interval_quot_neg_across_best l2 h2' _ _); assumption.
    + move: (classify_Across_inv _ _ Hnb2 Hc2) => [Hl2z Hh2z].
      apply: (interval_quot_across_across_best l2 h2 _ _); assumption.
Qed.

(** * The extracted form.

    [ZIntervalOps.interval_quot] reaches the same intervals in one flat
    dispatch: no [interval_opp] round-trips, no join to evaluate, and — for a
    divisor crossing zero — no division at all.  Proving it equal to the chain
    is what carries [interval_quot_unopt_best] over to the function that is
    actually extracted.

    Below the equality is algebra on [qb], the proof-free form of [quot_bound]
    introduced above.  Both sides reduce to pairs of [qb]s of the two operands'
    own bounds, and the negations push out to the top by [qb_neg_l] /
    [qb_neg_r], with no case analysis on the bounds at all in the seven
    sign-definite branches. *)

(** Unfold one case of the chain and push every negation out to the top, so
    that both sides are pairs of [qb]s of the two operands' own bounds. *)
Local Ltac qb_norm :=
  rewrite /interval_quot_across_pos /interval_quot_across_neg
          /interval_quot_neg_pos /interval_quot_pos_neg /interval_quot_neg_neg
          /interval_quot_pos /interval_opp /=;
  rewrite !quot_bound_qb ?qb_neg_l ?qb_neg_r ?qb_0_l ?bound_opp_involutive /=.

Lemma interval_quot_unopt_eq (i2 : interval) (i1 : nb_interval) :
  non_bottom i2 -> interval_quot i2 i1 = interval_quot_unopt i2 i1.
Proof.
  move: i2 => [l2 h2] Hnb2.
  rewrite /interval_quot /interval_quot_unopt.
  case: (classify_divisor i1) => [iP | iN | | Hl1 Hh1].
  - case: iP => [[l1 h1] [Hnb1 Hl1]]; simpl in Hnb1, Hl1.
    case Hc: (classify (l2, h2)) => /=.
    + by qb_norm.
    + by qb_norm.
    + (* Dividend crossing 0: both halves are divided by the divisor's low
         bound, and the inner ends of the join — the quotients of 0 — are
         absorbed, one half's quotients being non-positive and the other's
         non-negative. *)
      have [Hl2z Hh2z] := classify_Across_inv _ _ Hnb2 Hc.
      qb_norm; rewrite /ZInterval.join_lb /qb; clear Hc Hnb2.
      case: l1 Hnb1 Hl1 => [|l1]; case: l2 Hl2z => [|l2]; case: h2 Hh2z => [|h2];
        move=> *; unfold_set in *; simpl in *;
        solve [ contradiction | f_equal; f_equal; quot_signs; lia ].
  - case: iN => [[l1 h1] [Hnb1 Hh1]]; simpl in Hnb1, Hh1.
    case Hc: (classify (l2, h2)) => /=.
    + by qb_norm.
    + by qb_norm.
    + (* Mirror, for a strictly negative divisor: the two halves swap roles. *)
      have [Hl2z Hh2z] := classify_Across_inv _ _ Hnb2 Hc.
      qb_norm; rewrite /ZInterval.join_ub /qb; clear Hc Hnb2.
      case: h1 Hnb1 Hh1 => [|h1]; case: l2 Hl2z => [|l2]; case: h2 Hh2z => [|h2];
        move=> *; unfold_set in *; simpl in *;
        solve [ contradiction | f_equal; f_equal; quot_signs; lia ].
  - by [].
  - case Hc: (classify (l2, h2)) => /=.
    + move: (classify_Pos_inv _ _ Hc) => [l2' [Heq Hl2']]; subst.
      apply: (interval_quot_pos_across_opt_eq l2' h2 _); assumption.
    + move: (classify_Neg_inv _ _ Hc) => [h2' [Heq Hh2']]; subst.
      apply: (interval_quot_neg_across_opt_eq l2 h2' _); assumption.
    + by rewrite /interval_quot_across_across
                 /interval_quot_neg_across_opt /interval_quot_pos_across_opt.
Qed.

Lemma interval_quot_best (i2 : interval) (i1 : nb_interval) :
  non_bottom i2 ->
  classify_divisor i1 <> DivZero ->
  BestAbstraction (A:=itv) (interval_quot i2 i1)
    (collecting_quot (γ[itv] i2) (γ[itv] (`i1))).
Proof.
  move=> Hnb2 HnZ; rewrite (interval_quot_unopt_eq i2 i1 Hnb2).
  exact: interval_quot_unopt_best.
Qed.

(** A divisor of exactly [{0}] leaves the quotient's collecting semantics
    empty: every division is by zero, and [collecting_quot] excludes those.
    ([MulBackwardTheory] uses this to rule out [DivZero] from a witness.) *)
Lemma classify_divisor_zero_empty (i : nb_interval) (S2 : ℘ Z) c :
  classify_divisor i = DivZero -> ~ (c ∈ collecting_quot S2 (γ[itv] (`i))).
Proof.
  move=> Hcd Hc.
  have [_ Hback] := classify_divisor_quot_equiv i S2.
  move: (Hback c Hc); rewrite Hcd /classified_interval.
  by move=> [c2 [c1 [_ [Hc1 [_ _]]]]]; move: Hc1; unfold_set; simpl; lia.
Qed.

(** * The two limits of division.

    Division is α-complete but not exact, and — with a divisor crossing zero —
    not α-complete either.  The two examples below are the witnesses.

    First: the bounds of the result are the infimum and supremum of the
    collecting set, but γ of the result is strictly larger: [[4,4] ÷ [1,2] =
    [2,4]] while only [4 ÷ 1 = 4] and [4 ÷ 2 = 2] are realized — [3] is in the
    interval and in no quotient.  Exactness and α-completeness are independent
    notions (Abstraction.v); this is the witness that the second does not imply
    the first. *)
Example interval_quot_not_exact :
  ~ (forall (i2 : interval) (i1 : pos_interval),
       γ[itv] (interval_quot_pos i2 i1) ⊆ collecting_quot (γ[itv] i2) (γ[itv] (`i1))).
Proof.
  move=> Hex.
  set d := (WithTop.NotTop 4, WithTop.NotTop 4) : interval.
  set q := pos_itv 1 (WithTop.NotTop 2) ltac:(lia) ltac:(by simpl; lia).
  have Hq : interval_quot_pos d q = (WithTop.NotTop 2, WithTop.NotTop 4)
    by rewrite /interval_quot_pos /d /q /= !Primitives.quot_non_zero_quot.
  have Hk : 3 ∈ γ[itv] (interval_quot_pos d q)
    by rewrite Hq; unfold_set; simpl; lia.
  move: (Hex d q 3 Hk) => [c2 [c1 [Hc2 [Hc1 [_ Heq]]]]].
  unfold_set in Hc2; unfold_set in Hc1; simpl in Hc2, Hc1.
  have Hc2v : c2 = 4 by lia.
  have Hc1v : c1 = 1 \/ c1 = 2 by lia.
  by move: Heq; rewrite Hc2v; case: Hc1v => ->; vm_compute; lia.
Qed.

(** Second: α-completeness fails as soon as the divisor crosses zero, and no
    other transfer function would do better.

    α-completeness asks for a function of the two *abstract* values that is best
    for *every* pair of concrete sets they abstract.  For a monotone operation
    that is achievable, because the extremes of the image sit at the operands'
    glb and lub, which discreteness puts inside the sets
    ([itv_attained_low/high_witness]).  A quotient by a crossing divisor has its
    extremes at the divisor values *nearest zero* — interior points, whose
    presence an interval cannot certify.

    Concretely, [{-4, 4}] and [γ [-4,4]] have the same abstraction, but
    [{8} ÷ {-4,4} = {-2,2}] while [{8} ÷ γ [-4,4]] contains [8 ÷ 1 = 8].  One
    abstract value cannot be the best abstraction of both.

    So the γ-restriction on the across-divisor cases above is not a weakness of
    their proofs: it is forced.  What *can* be recovered is α-completeness
    relative to the nearest-to-zero bounds of the divisor's two sign halves —
    which is precisely the extra information a congruence or known-bits
    component supplies (see [todo/quot_alpha_completeness_shape.md]). *)

Example quot_across_no_alpha_complete :
  ~ (exists f : interval -> interval -> interval,
       forall (i2 i1 : interval) (S2 S1 : ℘ Z),
         IsAlpha (A:=itv) i2 S2 -> IsAlpha (A:=itv) i1 S1 ->
         IsAlpha (A:=itv) (f i2 i1) (collecting_quot S2 S1)).
Proof.
  move=> [f Hf].
  have Hd : IsAlpha (A:=itv) (WithTop.NotTop 8, WithTop.NotTop 8)
                    (γ[itv] (WithTop.NotTop 8, WithTop.NotTop 8))
    by apply: non_bottom_is_alpha_gamma; simpl; lia.
  have Hqg : IsAlpha (A:=itv) (WithTop.NotTop (-4), WithTop.NotTop 4)
                     (γ[itv] (WithTop.NotTop (-4), WithTop.NotTop 4))
    by apply: non_bottom_is_alpha_gamma; simpl; lia.
  have Hq : IsAlpha (A:=itv) (WithTop.NotTop (-4), WithTop.NotTop 4)
                    {[ z | z = -4 \/ z = 4 ]}.
  { apply: (is_alpha_itv_attained (-4) 4);
      [by unfold_set; left | by unfold_set; right |].
    by move=> c Hc; unfold_set in Hc; lia. }
  (* Against the two-point divisor, [[-2,2]] over-approximates, so the alleged
     best abstraction is below it. *)
  have Hle : f (WithTop.NotTop 8, WithTop.NotTop 8)
               (WithTop.NotTop (-4), WithTop.NotTop 4)
             ⊑[itv] (WithTop.NotTop (-2), WithTop.NotTop 2).
  { apply: ((Hf _ _ _ _ Hd Hq) (WithTop.NotTop (-2), WithTop.NotTop 2)).1.
    move=> z Hz; unfold_set in Hz.
    move: Hz => [c2 [c1 [Hc2 [Hc1 [_ Heq]]]]].
    unfold_set in Hc2; unfold_set in Hc1; simpl in Hc2, Hc1.
    have Hc2v : c2 = 8 by lia.
    have Hval : c2 ÷ c1 = -2 \/ c2 ÷ c1 = 2
      by rewrite Hc2v; case: Hc1 => ->; [left | right]; vm_compute.
    by rewrite -Heq; unfold_set; simpl; lia. }
  (* But against the whole interval [8 ÷ 1 = 8] is realized, so the same value
     would have to admit 8. *)
  have Hsub := ((Hf _ _ _ _ Hd Hqg) (WithTop.NotTop (-2), WithTop.NotTop 2)).2 Hle.
  have H8 : (8:Z) ∈ collecting_quot
                      (γ[itv] (WithTop.NotTop 8, WithTop.NotTop 8))
                      (γ[itv] (WithTop.NotTop (-4), WithTop.NotTop 4)).
  { exists 8, 1.
    split; [by unfold_set; simpl; lia|].
    split; [by unfold_set; simpl; lia|].
    by split; [lia | vm_compute]. }
  move: (Hsub _ H8) => Hmem; unfold_set in Hmem; simpl in Hmem; lia.
Qed.

End Interval_quot.

