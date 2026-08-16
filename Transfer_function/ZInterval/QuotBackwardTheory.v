(** QuotBackwardTheory.v - Backward (refinement) transfer functions for [Z.quot]
   on intervals. It is the composition of the abstractions of two parts:

     dividend [collecting_quot_backward_left] =
                 [collecting_binary_backward_left_partial is_nonzero Z.quot]

     divisor [collecting_quot_backward_right] =
                 [collecting_binary_backward_right_partial is_nonzero Z.quot].

   The computation of both is best, but the dividend computation is best only on
   the refined divisor. *)

(** * Divisor

   Intuitively, the divisor solve set is computed as divisor =
   dividend/quotient. However, we can't just reuse interval_quot: we have to
   return all the possible divisors that return the quotient.

   For instance, if quot 100 y = 3, then y is not just 100/3, but the interval
   [26,33] that contains all the divisors that can return 3.

   Because the divisor's solve set is convex, we can perform the intersection
   with the old divisor value and still be best. Let solve_set = the possible
   divisors computed from dividend and quotient. Then:

    hull(divisor ∩ solve_set)        // the true backward set
    = divisor ∩ solve_set            // both are intervals ⇒ intersection is an interval
    = divisor ∩ hull(solve_set)      // solve set convex ⇒ hull = set
    = meet divisor (solve divisor quotient) // meet is exact and γ(solve) = hull(solve_set)

   (the solve_set is convex, so a best abstraction of it represent it exactly). *)

(** * Dividend

    The dividend solve_set computation is dividend = divisor*quotient +
    remainder with |remainder| < |divisor|. This solve set is a union of blocks
    W(c1) — one per divisor value, each the interval of dividends whose quotient
    by c1 lands in γ quotient (convex by quot_window_iff). The union is
    non-convex, so meeting the hull with the incoming dividend re-admits gaps
    from blocks that miss it, and the result is therefore non-best:

    i1 = [2,3], i0 = [5,5]   →   solve set = [10,11] ∪ [15,17]
    γ solve = [10,17]   (the hull)
    i2 = [12,16]:  true backward set  [15,16],  meet = [12,16]   (loose)

    i2 lands in the gap between the two blocks; the meet lets the gap back in.

    The repair is not a sharper solve set (it is already best) but a smaller
    divisor. Refining the divisor first drops exactly the blocks whose W(c1)
    misses the incoming dividend; in that case, the covering lemma
    [itv_meet_is_alpha_covered] restores the equality:

    hull(dividend ∩ ⋃_{k feasible} W_k)
      // every surviving W_k meets dividend: hull commutes with ∩
    = dividend ∩ hull(⋃_{k feasible} W_k)
      // solve is best on the refined divisor
    = dividend ∩ γ(solve refined_divisor quot)
      // meet is exact
    = meet dividend (solve refined_divisor quot)
 *)

Require Import Abstraction AbstractLattice.
Require Import ssreflect ssrbool ssrfun.
Require Import BoundAbstraction.
Require Import AbstractionCombination.
Require Import BoundLattice.
Require Import autoreflect.
Require Import Tactics.
Require Import Quadrivalent.
From Stdlib Require Import Lia.
Require Import Stdlib.ZArith.ZArith.
Require Import ZTheory.
Require Import ZInterval.
Require Import ZIntervalTheory.
Require Import Transfer_function.ZInterval.ZIntervalOps.
Require Import Transfer_function.ZInterval.ZIntervalBackwardOps.
Require Import Transfer_function.ZInterval.AddTheory.
(* [interval_opp_preserves_non_bottom], for the divisor's negative half. *)
Require Import Transfer_function.ZInterval.MulTheory.
(* For the two sign halves of a zero-crossing interval, which the forward
   across-divisor cases already package: [gamma_itv_{neg,pos}_half] and
   [across_{neg,pos}_half_alpha]. *)
Require Import Transfer_function.ZInterval.OppTheory.
Require Import Transfer_function.ZInterval.QuotTheory.
Require Import Transfer_function.ZInterval.AddBackwardTheory.
Require Import Transfer_function.ZInterval.BackwardInterfaceTheory.

Open Scope Z_scope.
Generalizable All Variables.

(** * Arithmetic of truncated division.

    Two facts drive everything below, and both hinge on the same feature of
    C99-style truncation: the remainder carries the sign of the *dividend*, so
    it never cancels against [c1 * c0]. Plain [Z.quot_rem'] reasoning misses
    this and loses a factor of two on the dividend and the whole magnitude bound
    on the divisor. *)

(** When the quotient is non-zero, [|c0 * c1| ≥ |c1| > |Z.rem c2 c1|], so the
    remainder cannot pull [c2] across zero: [c2] has the sign of [c0 * c1], and
    therefore so does the remainder. *)
Lemma quot_rem_sign_nonneg (c2 c1 c0 : Z) :
  c1 <> 0 -> c0 <> 0 -> Z.quot c2 c1 = c0 -> 0 <= c0 * c1 ->
  0 <= Z.rem c2 c1.
Proof.
  move=> Hne1 Hne0 Heq Hpos.
  have Hdec : c2 = c0 * c1 + Z.rem c2 c1.
  { have := Z.quot_rem' c2 c1. rewrite Heq. lia. }
  have Hrb : Z.abs (Z.rem c2 c1) < Z.abs c1 by apply: Z.rem_bound_abs.
  case: (Z.le_gt_cases 0 c2) => Hc2s; first by apply: Z.rem_nonneg.
  exfalso.
  have Habs : Z.abs (c0 * c1) = Z.abs c0 * Z.abs c1 by apply: Z.abs_mul.
  have Hc0 : 1 <= Z.abs c0 by lia.
  have Hc1 : 1 <= Z.abs c1 by lia.
  nia.
Qed.

(** The mirror, by negating the dividend: [Z.quot] and [Z.rem] are both odd in
    it, so the [nonneg] case applied to [-c2] is this one. *)
Lemma quot_rem_sign_nonpos (c2 c1 c0 : Z) :
  c1 <> 0 -> c0 <> 0 -> Z.quot c2 c1 = c0 -> c0 * c1 <= 0 ->
  Z.rem c2 c1 <= 0.

Proof.
  move=> Hne1 Hne0 Heq Hneg.
  have := quot_rem_sign_nonneg (- c2) c1 (- c0) Hne1 (ltac:(lia))
    (ltac:(rewrite (Z.quot_opp_l c2 c1 Hne1) Heq; lia)) (ltac:(nia)).
  rewrite (Z.rem_opp_l c2 c1 Hne1).
  lia.
Qed.


(** * Magnitude bounds.

    [itv_max_abs] bounds the magnitude of the members.  The dividend's
    refinement is a magnitude bound and goes through it: its remainder window is
    the largest [|c1|].

    [itv_max_abs] is a proof-only view of what [quot_remainder_window_sym]
    computes inline; it is not extracted.  [quot_remainder_window_sym_eq] is the
    bridge that unfolds the computational definition into the
    [itv_max_abs]/[itv_sym] shape the lemmas below reason about. *)

Definition itv_max_abs (i : interval) : option Z :=
  match i with
  | (WithTop.NotTop l, WithTop.NotTop h) => Some (Z.max (Z.abs l) (Z.abs h))
  | _ => None end.

Definition itv_sym (b : Z) : interval := (WithTop.NotTop (- b), WithTop.NotTop b).

Lemma quot_remainder_window_sym_eq (i1 : interval) :
  quot_remainder_window_sym i1 =
    match itv_max_abs i1 with
    | None => itv_top
    | Some m => itv_sym (m - 1) end.
Proof.
  by case: i1 => [[|l] [|h]] //=; rewrite /itv_sym /itv_max_abs.
Qed.

Lemma itv_max_abs_sound (i : interval) (c m : Z) :
  itv_max_abs i = Some m -> c ∈ γ[itv] i -> Z.abs c <= m.
Proof.
  move: i => [[|l1] [|h1]] //= [<-] Hc; unfold_set in Hc; simpl in *; lia.
Qed.


(** * Refining the dividend — the solve step.

    This section is the solve step only: the dividends compatible with a divisor
    from [γ i1] and a quotient from [γ i0], with no incoming constraint on the
    dividend.  The transfer function refines the divisor first and then solves
    against the refined one — see §"Refining the dividend, after the divisor"
    below, and [todo/quot_backward_dividend.md].

    [c2] is determined by [c0] and [c1] up to the remainder, which
    [Z.rem_bound_abs] bounds by [|c1| - 1] — and, when the quotient cannot be
    zero, whose *sign* is pinned by the sign of the product, halving the window.

    The two summands are established separately: the product lands in the (best)
    abstract product, the remainder in the computed window.  Both are needed
    again, on arbitrary operand sets, by the α-completeness proof below. *)

Lemma quot_prod_in_mul (i1 i0 : interval) (c1 c0 : Z) :
  c1 ∈ γ[itv] i1 -> c0 ∈ γ[itv] i0 -> c0 * c1 ∈ γ[itv] (interval_mul i0 i1).
Proof.
  move=> Hc1 Hc0.
  have Hnb0 : non_bottom i0 by apply/non_bottom_non_empty; exists c0.
  have Hnb1 : non_bottom i1 by apply/non_bottom_non_empty; exists c1.
  have [Hover _] := interval_mul_best i0 i1 Hnb1 Hnb0.
  apply: Hover.
  unfold_set.
  by exists c0, c1.
Qed.

Lemma quot_rem_in_window (i1 i0 : interval) (c2 c1 c0 : Z) :
  c1 ∈ γ[itv] i1 -> c0 ∈ γ[itv] i0 -> c1 <> 0 -> Z.quot c2 c1 = c0 ->
  Z.rem c2 c1 ∈ γ[itv] (quot_remainder_window (interval_mul i0 i1) i1 i0).
Proof.
  move=> Hc1 Hc0 Hne Heq.
  have Hrb : Z.abs (Z.rem c2 c1) < Z.abs c1 by apply: Z.rem_bound_abs.
  have Hmul := quot_prod_in_mul i1 i0 c1 c0 Hc1 Hc0.
  (* The symmetric window always holds, since [|c1| ≤ max|γ i1|]. *)
  have Hsym : Z.rem c2 c1 ∈ γ[itv] (quot_remainder_window_sym i1).
  { rewrite quot_remainder_window_sym_eq.
    case Hm: (itv_max_abs i1) => [m|]; last by rewrite /itv_top; unfold_set.
    have := itv_max_abs_sound i1 c1 m Hm Hc1.
    rewrite /itv_sym; unfold_set; simpl; lia.
  }
  (* When the quotient cannot be zero, only half of it is needed. *)
  rewrite /quot_remainder_window.
  case Hz: (itv_gammab i0 0); first exact: Hsym.
  have Hc0n0 : c0 <> 0.
  { move=> Hz0.
    move: Hz.
    have -> : itv_gammab i0 0 = true by apply/itv_gammaP; rewrite -Hz0.
    done.
  } move: Hmul; case Hcl: (classify (interval_mul i0 i1)) => Hmul.
  - (* the product is non-negative, hence so is the remainder *) have Hp : 0 <= c0 * c1.
    { move: Hcl Hmul; move: (interval_mul i0 i1) => [lp hp] Hcl Hmul.
      have [l' [Hleq Hl'0]] := classify_Pos_inv _ _ Hcl.
      move: Hmul; rewrite Hleq => /gamma_itv_low Hlo; lia.
    } have Hr := quot_rem_sign_nonneg c2 c1 c0 Hne Hc0n0 Heq Hp.
    move: Hsym; move: (quot_remainder_window_sym i1) => [ls [|hs]] Hsym;
      unfold_set in Hsym; unfold_set; simpl in *; lia.
  - (* the product is non-positive, hence so is the remainder *) have Hp : c0 * c1 <= 0.
    { move: Hcl Hmul; move: (interval_mul i0 i1) => [lp hp] Hcl Hmul.
      have [h' [Hheq Hh'0]] := classify_Neg_inv _ _ Hcl.
      move: Hmul; rewrite Hheq => /gamma_itv_high Hhi; lia.
    } have Hr := quot_rem_sign_nonpos c2 c1 c0 Hne Hc0n0 Heq Hp.
    move: Hsym; move: (quot_remainder_window_sym i1) => [[|ls] hs] Hsym;
      unfold_set in Hsym; unfold_set; simpl in *; lia.
  - exact: Hsym.
Qed.

Lemma interval_quot_solve_dividend_sound (i1 i0 : interval) :
  Overapproximates (A:=itv)
    (interval_quot_solve_dividend i1 i0)
    (collecting_quot_solve_left (γ[itv] i1) (γ[itv] i0)).
Proof.
  move=> c2 Hc2.
  unfold_set in Hc2.
  move: Hc2 => [c1 [c0 [Hc1 [Hc0 [Hne Heq]]]]].
  have Hdecomp : c2 = c0 * c1 + Z.rem c2 c1.
  { have := Z.quot_rem' c2 c1.
    rewrite Heq.
    lia.
  } rewrite /interval_quot_solve_dividend.
  apply: interval_add_sound.
  unfold_set.
  exists (c0 * c1), (Z.rem c2 c1).
  split.
  - exact: quot_prod_in_mul.
  - split; last lia.
    exact: quot_rem_in_window Hc1 Hc0 Hne Heq.
Qed.

(** * α-completeness of the dividend, for a sign-definite divisor.

    [interval_quot_solve_dividend] does not merely over-approximate the solve
    set when the divisor cannot be zero: it computes its exact hull, and does so
    for *arbitrary* operand sets, not only for the concretizations of the two
    intervals.  That is the same statement [interval_add] enjoys, and it says
    that no extra knowledge about the divisors and quotients — a congruence, a
    set of known bits — can sharpen the interval component of the answer.

    The quotient's sign is unconstrained: the two theorems below,
    [interval_quot_solve_dividend_pos_alpha_complete] and [_neg_], cover the six
    sign quadrants between them.

    The proof is compositional, and deliberately so: the transfer function is
    [interval_add] applied to [interval_mul] and the remainder window, both
    already α-complete, so the α of the *Minkowski sum* [P + R] comes for free.
    But the sum is strictly larger than the solve set — it pairs the product of
    one divisor with the remainder window of another — so composition alone
    proves nothing.  What closes the gap is that both extremes of the sum are
    realised at a *single* divisor, the one of largest magnitude: both the
    product and the window grow with [|c1|], so the divisor that maximises one
    maximises the other.  [itv_same_alpha_same_bounds] then transports the α
    from the sum onto the solve set.

    This is exactly what fails once the divisor crosses zero: there the largest
    product wants the divisor of one sign and the largest remainder the other,
    and the computed interval is genuinely too wide (for [i1 = [-3,2]] and
    [i0 = [1,100]] it gives [[-302,202]] where the hull is [[-302,201]]).  Hence
    the sign hypothesis, which is also all that is needed: brute force over
    [[-10,10]] finds the computed interval exact on every box whose divisor
    excludes 0, and loose on none.

    Two things recur below and are worth naming in advance.

    - The [Top] bounds are why the bracket is used in its γ-transfer form
      ([itv_same_alpha_same_bounds]).  An unbounded divisor makes the solve set
      unbounded, so no witness inside it can bracket the sum; but the obligation
      "any bound of the solve set bounds the sum too" is discharged by [Top]
      immediately, and for a finite bound the goal is an inequality on [Z],
      which is [Stable] — so the CPS attainment lemmas apply.  [window_reached]
      packages the same trick: it is stated under [~~] precisely because an
      unbounded [S1] has no largest element to exhibit.

    - The quotient's sign enters only through a three-way disjunct
      ([quot_lower_disjunct_pos] and friends), which is what lets one theorem
      serve a positive, a negative *and* a zero-crossing quotient.
 *)

(** ** Sign of the abstract product.

    The window is one-sided only when [quot_remainder_window] can see that the
    product has a definite sign, so these four computations are what unlock it.
    [bcase] drives the boolean case analysis that [classify], [bound_mul] and
    [itv_gammab] are built from. *)

Local Ltac bcase :=
  repeat first [ match goal with
                 | H : context [Z.geb ?a ?b] |- _ =>
                     rewrite (Z.geb_leb a b) in H
                 | |- context [Z.geb ?a ?b] => rewrite (Z.geb_leb a b)
                 | H : context [Z.leb ?a ?b] |- _ =>
                     case: (Z.leb_spec0 a b) H => ? ?
                 | |- context [Z.leb ?a ?b] => case: (Z.leb_spec0 a b) => ?
                 | H : context [Z.eqb ?a ?b] |- _ =>
                     case: (Z.eqb_spec a b) H => ? ?
                 | |- context [Z.eqb ?a ?b] => case: (Z.eqb_spec a b) => ?
                 end ];
  simpl in *; try congruence; try lia; try nia.

Lemma classify_pos_of_low (l1 : Z) (h1 : WithTop.with_top Z) :
  0 < l1 -> classify (WithTop.NotTop l1, h1) = Pos.
Proof.
  move=> Hl1.
  rewrite /classify.
  by bcase.
Qed.

Lemma classify_neg_of_high (l1 : WithTop.with_top Z) (h1 : Z) :
  h1 < 0 -> non_bottom (l1, WithTop.NotTop h1) -> classify (l1, WithTop.NotTop h1) = Neg.
Proof.
  move: l1 => [|a] Hh1 Hnb; rewrite /classify; by bcase.
Qed.

(** [Across] is exactly the *strict* straddle: [classify] answers [Pos] on
    [[0,h]] and [Neg] on [[l,0]], so neither bound of an [Across] interval is [0]
    and no [non_bottom] hypothesis is needed.  Both directions are used below —
    the [->] to invert an arbitrary classification inside
    [interval_quot_solve_dividend_split_sound], the [<-] to reduce the transfer
    function on an [across_interval], whose payload is these two facts.
    ([classify_Across_inv], [ZIntervalTheory.v], gives the weaker non-strict
    reading and wants [non_bottom].) *)
Lemma classify_Across_of_signs (l h : WithTop.with_top Z) :
  low_neg l -> high_pos h -> classify (l, h) = Across.
Proof.
  move: l h => [|a] [|b] /= Hl Hh; rewrite /classify; by bcase.
Qed.

Lemma classify_Across_signs (l h : WithTop.with_top Z) :
  classify (l, h) = Across -> low_neg l /\ high_pos h.
Proof.
  move: l h => [|a] [|b]; rewrite /classify /= => H; (repeat split=> //); move: H; by bcase.
Qed.

Lemma classify_mul_pos_pos (l1 : Z) (h1 : WithTop.with_top Z) (i0 : interval) :
  0 < l1 -> classify i0 = Pos ->
  classify (interval_mul i0 (WithTop.NotTop l1, h1)) = Pos.
Proof.
  move: i0 => [l0 h0] Hl1 Hc0.
  rewrite /interval_mul (classify_pos_of_low l1 h1 Hl1) Hc0.
  rewrite /classify /bound_mul in Hc0 *.
  case: l0 Hc0 => [|b] Hc0; case: h0 Hc0 => [|d] Hc0; case: h1 => [|c]; bcase.
Qed.

Lemma classify_mul_pos_neg (l1 : Z) (h1 : WithTop.with_top Z) (i0 : interval) :
  0 < l1 -> non_bottom (WithTop.NotTop l1, h1) -> non_bottom i0 ->
  classify i0 = Neg ->
  classify (interval_mul i0 (WithTop.NotTop l1, h1)) = Neg.
Proof.
  move: i0 => [l0 h0] Hl1 Hnb1 Hnb0 Hc0.
  rewrite /interval_mul (classify_pos_of_low l1 h1 Hl1) Hc0.
  rewrite /classify /bound_mul /non_bottom in Hc0 Hnb0 Hnb1 *.
  case: l0 Hc0 Hnb0 => [|b] Hc0 Hnb0; case: h0 Hc0 Hnb0 => [|d] Hc0 Hnb0;
    case: h1 Hnb1 => [|c] Hnb1; bcase.
Qed.

Lemma classify_mul_neg_pos (l1 : WithTop.with_top Z) (h1 l0 : Z)
    (h0 : WithTop.with_top Z) :
  h1 < 0 -> 0 < l0 -> non_bottom (l1, WithTop.NotTop h1) ->
  non_bottom (WithTop.NotTop l0, h0) ->
  classify (interval_mul (WithTop.NotTop l0, h0) (l1, WithTop.NotTop h1)) = Neg.
Proof.
  move=> Hh1 Hl0 Hnb1 Hnb0.
  rewrite /interval_mul (classify_neg_of_high l1 h1 Hh1 Hnb1) (classify_pos_of_low l0 h0 Hl0).
  rewrite /classify /bound_mul /non_bottom in Hnb0 Hnb1 *.
  case: h0 Hnb0 => [|d] Hnb0; case: l1 Hnb1 => [|a] Hnb1; bcase.
Qed.

Lemma classify_mul_neg_neg (l1 : WithTop.with_top Z) (h1 : Z) (i0 : interval) :
  h1 < 0 -> non_bottom (l1, WithTop.NotTop h1) -> non_bottom i0 ->
  classify i0 = Neg ->
  classify (interval_mul i0 (l1, WithTop.NotTop h1)) = Pos.
Proof.
  move: i0 => [l0 h0] Hh1 Hnb1 Hnb0 Hc0.
  rewrite /interval_mul (classify_neg_of_high l1 h1 Hh1 Hnb1) Hc0.
  rewrite /classify /bound_mul /non_bottom in Hc0 Hnb0 Hnb1 *.
  case: l0 Hc0 Hnb0 => [|b] Hc0 Hnb0; case: h0 Hc0 Hnb0 => [|d] Hc0 Hnb0;
    case: l1 Hnb1 => [|a] Hnb1; bcase.
Qed.

(** ** The remainder window, and the magnitude it allows. *)

Lemma itv_gammab_zero_pos (v : Z) (h0 : WithTop.with_top Z) :
  0 < v -> itv_gammab (WithTop.NotTop v, h0) 0 = false.
Proof.
  move=> Hv.
  rewrite /itv_gammab /glb_gammab.
  by have -> : (v <=? 0) = false by apply/Z.leb_gt; lia.
Qed.

Lemma itv_gammab_zero_neg (l0 : WithTop.with_top Z) (v : Z) :
  v < 0 -> itv_gammab (l0, WithTop.NotTop v) 0 = false.
Proof.
  move=> Hv.
  rewrite /itv_gammab /lub_gammab.
  have -> : (0 <=? v) = false by apply/Z.leb_gt; lia.
  by rewrite andbF.
Qed.

Lemma itv_max_abs_ge_one_pos (l1 : Z) (h1 : WithTop.with_top Z) (m : Z) :
  0 < l1 -> itv_max_abs (WithTop.NotTop l1, h1) = Some m -> 1 <= m.
Proof.
  case: h1 => [|hh] //= Hl1 [<-]; lia.
Qed.

Lemma itv_max_abs_pos (l1 hh : Z) :
  0 < l1 -> l1 <= hh ->
  itv_max_abs (WithTop.NotTop l1, WithTop.NotTop hh) = Some hh.

Proof.
  move=> H1 H2.
  rewrite /itv_max_abs.
  f_equal.
  lia.
Qed.

Lemma quot_remainder_window_non_bottom (p i1 i0 : interval) :
  (forall m, itv_max_abs i1 = Some m -> 1 <= m) ->
  non_bottom (quot_remainder_window p i1 i0).
Proof.
  move=> Hm.
  rewrite /quot_remainder_window quot_remainder_window_sym_eq.
  case Hma: (itv_max_abs i1) => [m|].
  - have := Hm m Hma.
    rewrite /itv_sym.
    case: (itv_gammab i0 0) => /=; first lia.
    case: (classify p) => /=; lia.
  - by case: (itv_gammab i0 0) => /=; case: (classify p) => /=.
Qed.

Lemma quot_remainder_window_abs_bound (p i1 i0 : interval) (r m : Z) :
  itv_max_abs i1 = Some m -> r ∈ γ[itv] (quot_remainder_window p i1 i0) ->
  Z.abs r <= m - 1.
Proof.
  move=> Hm.
  rewrite /quot_remainder_window quot_remainder_window_sym_eq Hm /itv_sym.
  case: (itv_gammab i0 0); first by unfold_set; simpl; lia.
  case: (classify p); unfold_set; simpl; lia.
Qed.

Lemma quot_remainder_window_sign_nonneg (p i1 i0 : interval) (r : Z) :
  itv_gammab i0 0 = false -> classify p = Pos ->
  r ∈ γ[itv] (quot_remainder_window p i1 i0) -> 0 <= r.
Proof.
  rewrite /quot_remainder_window => -> ->.
  by move: (quot_remainder_window_sym i1) => [ls hs] /=[].
Qed.

Lemma quot_remainder_window_sign_nonpos (p i1 i0 : interval) (r : Z) :
  itv_gammab i0 0 = false -> classify p = Neg ->
  r ∈ γ[itv] (quot_remainder_window p i1 i0) -> r <= 0.
Proof.
  rewrite /quot_remainder_window => -> ->.
  by move: (quot_remainder_window_sym i1) => [ls hs] /=[].
Qed.

(** ** The two extreme members of the solve set.

    [quot_solve_witness_exact] pins the dividend with remainder [0]; the other
    two pin the dividends whose remainder is as large as the divisor allows, on
    whichever side the sign of the product puts it. *)

Lemma quot_solve_witness_exact (S1 S0 : ℘ Z) (c1 c0 : Z) :
  c1 ∈ S1 -> c0 ∈ S0 -> c1 <> 0 -> c0 * c1 ∈ collecting_quot_solve_left S1 S0.
Proof.
  move=> Hc1 Hc0 Hne.
  unfold_set.
  exists c1, c0.
  do 3 (split=> //).
  exact: Z.quot_mul.
Qed.

Lemma quot_up_identity (c1 c0 : Z) :
  c1 <> 0 -> 0 <= c0 * c1 -> Z.quot (c0 * c1 + (Z.abs c1 - 1)) c1 = c0.
Proof.
  move=> Hne Hsgn.
  case: (Z.lt_ge_cases c1 0) => Hc1s.
  - have Habs : Z.abs c1 = - c1 by lia.
    rewrite Habs.
    have Hpos : Z.quot (c0 * c1 + (- c1 - 1)) (- c1) = - c0
      by symmetry; apply: (Z.quot_unique (c0 * c1 + (- c1 - 1)) (- c1) (- c0) (- c1 - 1)); nia.
    have Hflip := Z.quot_opp_r (c0 * c1 + (- c1 - 1)) (- c1) (ltac:(lia)).
    rewrite Z.opp_involutive in Hflip.
    rewrite Hflip Hpos.
    lia.
  - have Habs : Z.abs c1 = c1 by lia.
    rewrite Habs.
    symmetry.
    apply: (Z.quot_unique (c0 * c1 + (c1 - 1)) c1 c0 (c1 - 1)); nia.
Qed.

Lemma quot_down_identity (c1 c0 : Z) :
  c1 <> 0 -> c0 * c1 <= 0 -> Z.quot (c0 * c1 - (Z.abs c1 - 1)) c1 = c0.
Proof.
  move=> Hne Hsgn.
  have -> : c0 * c1 - (Z.abs c1 - 1) = - ((- c0) * c1 + (Z.abs c1 - 1)) by lia.
  rewrite (Z.quot_opp_l ((- c0) * c1 + (Z.abs c1 - 1)) c1 Hne).
  by rewrite (quot_up_identity c1 (- c0) Hne (ltac:(nia))); lia.
Qed.

Lemma quot_solve_witness_up (S1 S0 : ℘ Z) (c1 c0 : Z) :
  c1 ∈ S1 -> c0 ∈ S0 -> c1 <> 0 -> 0 <= c0 * c1 ->
  c0 * c1 + (Z.abs c1 - 1) ∈ collecting_quot_solve_left S1 S0.
Proof.
  move=> Hc1 Hc0 Hne Hsgn.
  unfold_set.
  exists c1, c0.
  do 3 (split=> //).
  exact: quot_up_identity.
Qed.

Lemma quot_solve_witness_down (S1 S0 : ℘ Z) (c1 c0 : Z) :
  c1 ∈ S1 -> c0 ∈ S0 -> c1 <> 0 -> c0 * c1 <= 0 ->
  c0 * c1 - (Z.abs c1 - 1) ∈ collecting_quot_solve_left S1 S0.
Proof.
  move=> Hc1 Hc0 Hne Hsgn.
  unfold_set.
  exists c1, c0.
  do 3 (split=> //).
  exact: quot_down_identity.
Qed.

(** ** Reaching the divisor that realises the window. *)

(** [S1] contains a divisor that dominates [c1] in magnitude and leaves room for
    a window of [N].  Stated under [~~] because an unbounded [S1] has no largest
    element to exhibit; every use site has a [Stable] goal.  The magnitude
    comparison is written [c1 * c1 <= c1 * m] rather than with [Z.abs] so that it
    carries the "same sign as [c1]" part too, and so that [nia] can use it. *)
Definition window_reached (S1 : ℘ Z) (c1 N : Z) : Prop :=
  ~ ~ exists m, m ∈ S1 /\ c1 * c1 <= c1 * m /\ N <= Z.abs m - 1.

Lemma window_reached_pos (l1 : Z) (h1 : WithTop.with_top Z) (S1 : ℘ Z) (c1 N : Z) :
  0 < l1 ->
  IsAlpha (A:=itv) (WithTop.NotTop l1, h1) S1 ->
  (exists c, c ∈ S1) -> c1 ∈ S1 -> (forall hh, h1 = WithTop.NotTop hh -> N <= hh - 1) ->
  window_reached S1 c1 N.
Proof.
  move=> Hl1 Ha1 Hex1 Hc1 HN.
  have Hs1 := gamma_alpha_extensive itv _ _ Ha1.
  have Hc1p : 0 < c1 by have := gamma_itv_low _ _ _ (Hs1 _ Hc1); lia.
  case: h1 Ha1 Hs1 HN => [|hh] Ha1 Hs1 HN.
  - move: (Ha1) => /Conjunction.is_alpha_pair_iff [_ Hlub].
    apply: (is_alpha_lubtop_top_witness S1 (Z.max N (Z.abs c1)) Hlub) => [] [m [Hm HmM]].
    move=> Hn; apply: Hn.
    exists m.
    split=> //.
    nia.
  - apply: (itv_attained_high_witness (WithTop.NotTop l1) (WithTop.NotTop hh) S1 Ha1 Hex1) => Hath.
    have Hc1h : c1 <= hh by move: (Hs1 _ Hc1); exact: gamma_itv_high.
    have := HN hh erefl.
    move=> Hb Hn; apply: Hn.
    exists hh.
    split=> //.
    nia.
Qed.

(** No [window_reached_neg]: a negative divisor is handled by negating the
    divisor and the quotient together, not by mirroring the argument — see
    [interval_quot_solve_dividend_neg_alpha_complete]. *)

(** ** Transferring a bound from the solve set to the Minkowski sum.

    One lemma per direction, for both divisor signs.  The disjunct is what makes
    them sign-agnostic in the *quotient*: either the product already points the
    right way, or the window does, or [S0] contains a quotient whose product
    does.

    It is named because it is stated four times — twice as a hypothesis here,
    twice as the conclusion of a [quot_*_disjunct_pos] lemma below — and because
    "the disjunct" is what the next section is about.  What each buys is a
    *single* divisor at which the corresponding extreme of the sum is realised.
 *)

Definition upper_disjunct (S0 : ℘ Z) (c0 c1 r : Z) :
  Prop := 0 <= c0 * c1 \/ r <= 0 \/ (exists c0', c0' ∈ S0 /\ 0 <= c0' * c1).

Definition lower_disjunct (S0 : ℘ Z) (c0 c1 r : Z) : Prop
  := c0 * c1 <= 0 \/ 0 <= r \/ (exists c0', c0' ∈ S0 /\ c0' * c1 <= 0).

Lemma quot_solve_upper (S1 S0 : ℘ Z) (M c0 c1 r : Z) :
  c1 ∈ S1 -> c0 ∈ S0 -> c1 <> 0 -> upper_disjunct S0 c0 c1 r ->
  window_reached S1 c1 r ->
  (forall v, v ∈ collecting_quot_solve_left S1 S0 -> v <= M) ->
  c0 * c1 + r <= M.
Proof.
  move=> Hc1 Hc0 Hne Hdisj Hreach Hb.
  case: (Z.le_gt_cases r 0) => Hr.
  { have := Hb _ (quot_solve_witness_exact S1 S0 c1 c0 Hc1 Hc0 Hne).
    lia.
  } have [c0' [Hc0'S [Hc0'sgn Hc0'dom]]] :
      exists c0', c0' ∈ S0 /\ 0 <= c0' * c1 /\ c0 * c1 <= c0' * c1.
  { case: (Z.le_gt_cases 0 (c0 * c1)) => Hprod.
    - exists c0.
      split=> //.
      split=> //.
      lia.
    - case: Hdisj => [Hd|[Hd|[x [Hx Hxs]]]]; [exfalso; lia | exfalso; lia |].
      exists x.
      split=> //.
      split=> //.
      lia.
  } apply: stable => Hng.
  apply: Hreach => [] [m [Hm [Hdom HN]]].
  apply: Hng.
  have Hm0 : m <> 0 by nia.
  have Hsgnm : 0 <= c0' * m by nia.
  have Hv := Hb _ (quot_solve_witness_up S1 S0 m c0' Hm Hc0'S Hm0 Hsgnm).
  nia.
Qed.

Lemma quot_solve_lower (S1 S0 : ℘ Z) (m0 c0 c1 r : Z) :
  c1 ∈ S1 -> c0 ∈ S0 -> c1 <> 0 -> lower_disjunct S0 c0 c1 r ->
  window_reached S1 c1 (- r) ->
  (forall v, v ∈ collecting_quot_solve_left S1 S0 -> m0 <= v) ->
  m0 <= c0 * c1 + r.
Proof.
  move=> Hc1 Hc0 Hne Hdisj Hreach Hb.
  case: (Z.le_gt_cases 0 r) => Hr.
  { have := Hb _ (quot_solve_witness_exact S1 S0 c1 c0 Hc1 Hc0 Hne).
    lia.
  } have [c0' [Hc0'S [Hc0'sgn Hc0'dom]]] :
      exists c0', c0' ∈ S0 /\ c0' * c1 <= 0 /\ c0' * c1 <= c0 * c1.
  { case: (Z.le_gt_cases (c0 * c1) 0) => Hprod.
    - exists c0.
      split=> //.
      split=> //.
      lia.
    - case: Hdisj => [Hd|[Hd|[x [Hx Hxs]]]]; [exfalso; lia | exfalso; lia |].
      exists x.
      split=> //.
      split=> //.
      lia.
  } apply: stable => Hng.
  apply: Hreach => [] [m [Hm [Hdom HN]]].
  apply: Hng.
  have Hm0 : m <> 0 by nia.
  have Hsgnm : c0' * m <= 0 by nia.
  have Hv := Hb _ (quot_solve_witness_down S1 S0 m c0' Hm Hc0'S Hm0 Hsgnm).
  nia.
Qed.

(** ** Discharging the disjunct.

    This is where the quotient's sign is spent, and the only place the quotient
    interval is taken apart: either it reaches far enough on the relevant side of
    zero for [S0] to supply the needed quotient, or it is sign-definite, and then
    the product's sign clamps the window. *)

(** With a positive divisor, only the [pos] pair is needed: a negative divisor
    is reached by negating the divisor and the quotient together
    ([interval_quot_solve_dividend_neg_alpha_complete]), which leaves the solve
    set alone, so there is no [_neg] mirror of either. *)

Lemma quot_lower_disjunct_pos (l1 : Z) (h1 : WithTop.with_top Z) (i0 : interval)
    (S0 : ℘ Z) (c0 c1 r : Z) :
  0 < l1 -> IsAlpha (A:=itv) i0 S0 -> (exists c, c ∈ S0) -> c0 ∈ S0 ->
  0 < c1 ->
  r ∈ γ[itv] (quot_remainder_window (interval_mul i0 (WithTop.NotTop l1, h1))
    (WithTop.NotTop l1, h1) i0) ->
  ~ ~ lower_disjunct S0 c0 c1 r.

Proof.
  move=> Hl1 Ha0 Hex0 Hc0 Hc1p Hr.
  case: (Z.le_gt_cases c0 0) => Hc0s; first by move=> Hn; apply: Hn; left; nia.
  case: i0 Ha0 Hr => [l0 h0] Ha0 Hr.
  case: l0 Ha0 Hr => [|v] Ha0 Hr.
  - move: (Ha0) => /Conjunction.is_alpha_pair_iff [Hglb _].
    move=> Hn.
    apply: (is_alpha_glbtop_top_nn S0 0 Hglb) => [] [c0' [Hc0' Hlt]].
    apply: Hn.
    right; right.
    exists c0'.
    split=> //.
    nia.
  - case: (Z.le_gt_cases v 0) => Hv.
    + move=> Hn.
      apply: (itv_attained_low_witness (WithTop.NotTop v) h0 S0 Ha0 Hex0) => Hatl.
      apply: Hn.
      right; right.
      exists v.
      split=> //.
      nia.
    + move=> Hn.
      apply: Hn.
      right; left.
      apply: (quot_remainder_window_sign_nonneg _ (WithTop.NotTop l1, h1)
        (WithTop.NotTop v, h0)) => //.
      * exact: itv_gammab_zero_pos.
      * exact: (classify_mul_pos_pos l1 h1 _ Hl1 (classify_pos_of_low v h0 Hv)).
      * exact: Hr.
Qed.

Lemma quot_upper_disjunct_pos (l1 : Z) (h1 : WithTop.with_top Z) (i0 : interval)
    (S0 : ℘ Z) (c0 c1 r : Z) :
  0 < l1 -> non_bottom (WithTop.NotTop l1, h1) -> non_bottom i0 ->
  IsAlpha (A:=itv) i0 S0 -> (exists c, c ∈ S0) -> c0 ∈ S0 -> 0 < c1 ->
  r ∈ γ[itv] (quot_remainder_window (interval_mul i0 (WithTop.NotTop l1, h1))
    (WithTop.NotTop l1, h1) i0) ->
  ~ ~ upper_disjunct S0 c0 c1 r.

Proof.
  move=> Hl1 Hnb1 Hnb0 Ha0 Hex0 Hc0 Hc1p Hr.
  case: (Z.le_gt_cases 0 c0) => Hc0s; first by move=> Hn; apply: Hn; left; nia.
  case: i0 Hnb0 Ha0 Hr => [l0 h0] Hnb0 Ha0 Hr.
  case: h0 Hnb0 Ha0 Hr => [|v] Hnb0 Ha0 Hr.
  - move: (Ha0) => /Conjunction.is_alpha_pair_iff [_ Hlub].
    move=> Hn.
    apply: (is_alpha_lubtop_top_nn S0 0 Hlub) => [] [c0' [Hc0' Hlt]].
    apply: Hn.
    right; right.
    exists c0'.
    split=> //.
    nia.
  - case: (Z.le_gt_cases 0 v) => Hv.
    + move=> Hn.
      apply: (itv_attained_high_witness l0 (WithTop.NotTop v) S0 Ha0 Hex0) => Hath.
      apply: Hn.
      right; right.
      exists v.
      split=> //.
      nia.
    + move=> Hn.
      apply: Hn.
      right; left.
      apply: (quot_remainder_window_sign_nonpos _ (WithTop.NotTop l1, h1)
        (l0, WithTop.NotTop v)) => //.
      * apply: itv_gammab_zero_neg.
        lia.
      * apply: (classify_mul_pos_neg l1 h1 _ Hl1 Hnb1 Hnb0).
        apply: classify_neg_of_high => //.
      * exact: Hr.
Qed.

(** ** The two theorems. *)

Lemma interval_quot_solve_dividend_pos_alpha_complete (l1 : Z)
    (h1 : WithTop.with_top Z) (i0 : interval) (S1 S0 : ℘ Z) :
  0 < l1 -> (exists c, c ∈ S1) -> (exists c, c ∈ S0) ->
  binary_alpha_complete itv itv itv interval_quot_solve_dividend
    collecting_quot_solve_left (WithTop.NotTop l1, h1) i0 S1 S0.

Proof.
  rewrite /binary_alpha_complete => Hl1 Hex1 Hex0 Ha1 Ha0.
  have Hnb1 : non_bottom (WithTop.NotTop l1, h1)
    by move: Hex1 => [c Hc]; exact: non_bottom_of_alpha Ha1 Hc.
  have Hnb0 : non_bottom i0 by move: Hex0 => [c Hc]; exact: non_bottom_of_alpha Ha0 Hc.
  have Hs1 := gamma_alpha_extensive itv _ _ Ha1.
  have Hs0 := gamma_alpha_extensive itv _ _ Ha0.
  have Hp1 : forall c, c ∈ S1 -> 0 < c by move=> c Hc; have := gamma_itv_low _ _ _ (Hs1 _ Hc); lia.
  rewrite /interval_quot_solve_dividend.
  set p := interval_mul i0 (WithTop.NotTop l1, h1).
  set s := quot_remainder_window p (WithTop.NotTop l1, h1) i0.
  set T := collecting_quot_solve_left S1 S0.
  set P := collecting_binary_forward Z.mul S0 S1.
  have Hnbs : non_bottom s
    by rewrite /s; apply: quot_remainder_window_non_bottom => m Hm;
      exact: (itv_max_abs_ge_one_pos l1 h1 m Hl1 Hm).
  have Hbound : forall r, r ∈ γ[itv] s -> forall hh, h1 = WithTop.NotTop hh -> Z.abs r <= hh - 1.
  { move=> r Hr hh Hhh.
    apply: (quot_remainder_window_abs_bound p (WithTop.NotTop l1, h1) i0 r hh) => //.
    rewrite Hhh.
    apply: itv_max_abs_pos => //.
    move: Hnb1.
    rewrite Hhh /=.
    lia.
  } have HexP : exists c, c ∈ P.
  { move: Hex0 Hex1 => [a Ha] [b Hb].
    exists (a * b).
    rewrite /P.
    unfold_set.
    by exists a, b.
  } have HexR : exists c, c ∈ γ[itv] s by apply/non_bottom_non_empty.
  have HP : IsAlpha (A:=itv) p P
    by exact: (interval_mul_alpha_complete i0 _ S0 S1 Hnb1 Hnb0 Hex0 Hex1 Ha0 Ha1).
  have HR : IsAlpha (A:=itv) s (γ[itv] s) by exact: non_bottom_is_alpha_gamma.
  have HSum := interval_add_alpha_complete p s P (γ[itv] s) HexP HexR HP HR.
  have Hsub : T ⊆ collecting_binary_forward Z.add P (γ[itv] s).
  { move=> c2.
    rewrite /T => Hc2.
    unfold_set in Hc2.
    move: Hc2 => [c1 [c0 [Hc1 [Hc0 [Hne Heq]]]]].
    unfold_set.
    exists (c0 * c1), (Z.rem c2 c1).
    split.
    - rewrite /P.
      unfold_set.
      by exists c0, c1.
    - split; last by have := Z.quot_rem' c2 c1; rewrite Heq; lia.
      exact: quot_rem_in_window (Hs1 _ Hc1) (Hs0 _ Hc0) Hne Heq.
  } have Hglb : forall b : glbtop, T ⊆ γ[glbtop] b ->
      collecting_binary_forward Z.add P (γ[itv] s) ⊆ γ[glbtop] b.
  { case=> [|m0] Hb z Hz; first by unfold_set.
    unfold_set in Hz.
    move: Hz => [q [r [Hq [Hr Hz]]]].
    rewrite /P in Hq.
    unfold_set in Hq.
    move: Hq => [c0 [c1 [Hc0 [Hc1 Hq]]]].
    have Hc1p := Hp1 _ Hc1.
    have Hgoal : m0 <= z -> z ∈ γ[glbtop] (WithTop.NotTop m0) by unfold_set; simpl; lia.
    apply: Hgoal.
    apply: stable => Hng.
    apply: (quot_lower_disjunct_pos l1 h1 i0 S0 c0 c1 r Hl1 Ha0 Hex0 Hc0 Hc1p Hr) => Hdisj.
    apply: Hng.
    have Hle := quot_solve_lower S1 S0 m0 c0 c1 r Hc1 Hc0 (ltac:(lia)) Hdisj
      (window_reached_pos l1 h1 S1 c1 (- r) Hl1 Ha1 Hex1 Hc1
        (ltac:(move=> hh Hhh; have := Hbound r Hr hh Hhh; lia)))
      (ltac:(move=> v Hv; have := Hb _ Hv; by unfold_set; simpl)).
    lia.
  } have Hlub : forall b : lubtop, T ⊆ γ[lubtop] b -> collecting_binary_forward Z.add P (γ[itv] s) ⊆ γ[lubtop] b.
  { case=> [|M] Hb z Hz; first by unfold_set.
    unfold_set in Hz.
    move: Hz => [q [r [Hq [Hr Hz]]]].
    rewrite /P in Hq.
    unfold_set in Hq.
    move: Hq => [c0 [c1 [Hc0 [Hc1 Hq]]]].
    have Hc1p := Hp1 _ Hc1.
    have Hgoal : z <= M -> z ∈ γ[lubtop] (WithTop.NotTop M) by unfold_set; simpl; lia.
    apply: Hgoal.
    apply: stable => Hng.
    apply: (quot_upper_disjunct_pos l1 h1 i0 S0 c0 c1 r Hl1 Hnb1 Hnb0 Ha0 Hex0
      Hc0 Hc1p Hr) => Hdisj.
    apply: Hng.
    have Hle := quot_solve_upper S1 S0 M c0 c1 r Hc1 Hc0 (ltac:(lia)) Hdisj
      (window_reached_pos l1 h1 S1 c1 r Hl1 Ha1 Hex1 Hc1
        (ltac:(move=> hh Hhh; have := Hbound r Hr hh Hhh; lia)))
      (ltac:(move=> v Hv; have := Hb _ Hv; by unfold_set; simpl)).
    lia.
  } exact: (proj2 (itv_same_alpha_same_bounds _ T (interval_add p s) Hsub Hglb Hlub) HSum).
Qed.

(** ** The negative divisor, by negation.

    Negating the divisor negates the *quotient*, not the dividend —
    [c2 ÷ (-c1) = -(c2 ÷ c1)] — so negating both operand sets leaves the
    dividend solve set exactly where it was.  The transfer function is invariant
    the same way, and the negative-divisor theorem is then the positive one read
    through [is_alpha_opp_iff], with no second copy of the bracket argument.

    This is the manoeuvre [interval_quot_solve_divisor_neg_sound] already makes
    on the divisor side, and the one the forward file makes for three of its
    four quotient quarters ([QuotTheory.v]).
 *)

Lemma collecting_quot_solve_left_opp (S1 S0 : ℘ Z) :
  collecting_quot_solve_left {[ z | -z ∈ S1 ]} {[ z | -z ∈ S0 ]} ⊆⊇
  collecting_quot_solve_left S1 S0.

Proof.
  unfold_set_equiv => c2; split; move=> [c1 [c0 [Hc1 [Hc0 [Hne Heq]]]]];
    exists (- c1), (- c0); unfold_set; rewrite ?Z.opp_involutive
      (Z.quot_opp_r c2 c1 Hne);
    by repeat split => //; rewrite /is_nonzero in Hne *; lia.
Qed.

(** [itv_max_abs] and "does γ contain 0" are both negation-invariant, and the
    product is too ([interval_mul_opp_opp]) — which is everything
    [interval_quot_solve_dividend] reads. *)
Lemma itv_max_abs_opp (i : interval) : itv_max_abs (interval_opp i) = itv_max_abs i.

Proof.
  move: i => [[|l] [|h]] //=.
  f_equal.
  lia.
Qed.

Lemma itv_gammab_opp_zero (i : interval) : itv_gammab (interval_opp i) 0 = itv_gammab i 0.

Proof.
  move: i => [[|l] [|h]]; rewrite /itv_gammab /glb_gammab /lub_gammab /=; bcase; by rewrite andbC.
Qed.

Lemma interval_quot_solve_dividend_opp_opp (i1 i0 : interval) :
  non_bottom i1 -> non_bottom i0 ->
  interval_quot_solve_dividend (interval_opp i1) (interval_opp i0) =
  interval_quot_solve_dividend i1 i0.

Proof.
  move=> Hnb1 Hnb0.
  rewrite /interval_quot_solve_dividend (interval_mul_opp_opp i0 i1 Hnb1 Hnb0)
    /quot_remainder_window !quot_remainder_window_sym_eq !itv_max_abs_opp
    itv_gammab_opp_zero.
  by [].
Qed.

Lemma interval_quot_solve_dividend_neg_alpha_complete (l1 : WithTop.with_top Z)
    (h1 : Z) (i0 : interval) (S1 S0 : ℘ Z) :
  h1 < 0 -> (exists c, c ∈ S1) -> (exists c, c ∈ S0) ->
  binary_alpha_complete itv itv itv interval_quot_solve_dividend
    collecting_quot_solve_left (l1, WithTop.NotTop h1) i0 S1 S0.

Proof.
  rewrite /binary_alpha_complete => Hh1 Hex1 Hex0 Ha1 Ha0.
  have Hnb1 : non_bottom (l1, WithTop.NotTop h1)
    by move: Hex1 => [c Hc]; exact: non_bottom_of_alpha Ha1 Hc.
  have Hnb0 : non_bottom i0 by move: Hex0 => [c Hc]; exact: non_bottom_of_alpha Ha0 Hc.
  (* The negated divisor is strictly positive, so the [pos] theorem applies to
     the two negated operand sets. *)
  have Hpos := interval_quot_solve_dividend_pos_alpha_complete (- h1)
    (bound_opp l1) (interval_opp i0) {[ z | -z ∈ S1 ]} {[ z | -z ∈ S0 ]}
    ltac:(lia) (opp_nonempty _ Hex1) (opp_nonempty _ Hex0)
    ((is_alpha_opp_iff _ _).1 Ha1) ((is_alpha_opp_iff _ _).1 Ha0).
  rewrite -(interval_quot_solve_dividend_opp_opp _ i0 Hnb1 Hnb0).
  exact: (is_alpha_set_equiv _ _ _ (collecting_quot_solve_left_opp S1 S0) Hpos).
Qed.

(** ** Divisors that are only *almost* sign-definite.

    A divisor set whose abstraction has [0] on a bound — [[0,h1]], or anything
    a richer domain reduces to that — is not covered by the two theorems as
    stated, and yet needs no new arithmetic: the guard has already discarded the
    zero divisors, so the solve set is the one of the *non-zero* part of [S1],
    and that part is sign-definite.  What the theorems need is therefore an
    abstraction of [S1 ∖ {0}], and the honest place to get it is the caller:
    which zero an abstraction can remove is a property of the abstraction, not
    of division.  An interval can drop a [0] sitting on a bound, by the ∓1 clamp
    ([ZInterval.itv_strictly_positive_part] and its negative twin); a congruence
    does better ([≡ 0 mod 4] on [[-4,0]] is [[-4,-4]], where the interval can
    only say [[-4,-1]]); so [i1'] is an input here, not something computed.

    Note what these two do *not* say.  [interval_quot_solve_dividend_split] does
    clamp its divisor off zero, so on [i1 = [0,h1]] it is best
    ([interval_quot_solve_dividend_split_best]) — but only at γ.  An arbitrary
    [S1] with hull [[0,h1]] need not contain the [1] the clamp claims, and then
    the interval is honestly too wide: [S1 = {-4,0}] against [S0 = {-4}] solves
    to [[16,19]] where [[-4,-1]] forces [[4,19]].  That is the gap these two
    close, and the reason the sanitized divisor is an input: only the
    abstraction knows which zero it can really remove.
 *)

Lemma quot_solve_left_drop_zero (S1 S0 : ℘ Z) :
  collecting_quot_solve_left S1 S0 ⊆⊇
  collecting_quot_solve_left {[ c1 | c1 ∈ S1 /\ c1 <> 0 ]} S0.

Proof.
  apply: collecting_binary_solve_left_partial_restrict.
  - by move=> c1; unfold_set; move=> [].
  - by move=> c2 c1 Hc1 HP; unfold_set.
Qed.

Lemma interval_quot_solve_dividend_pos_nonzero_alpha_complete (l1 : Z)
    (h1 : WithTop.with_top Z) (i0 : interval) (S1 S0 : ℘ Z) :
  0 < l1 -> (exists c, c ∈ S1 /\ c <> 0) -> (exists c, c ∈ S0) ->
  IsAlpha (A:=itv) (WithTop.NotTop l1, h1) {[ c1 | c1 ∈ S1 /\ c1 <> 0 ]} ->
  IsAlpha (A:=itv) i0 S0 ->
  IsAlpha (A:=itv) (interval_quot_solve_dividend (WithTop.NotTop l1, h1) i0)
    (collecting_quot_solve_left S1 S0).

Proof.
  move=> Hl1 [c [Hc Hc0]] Hex0 Ha1 Ha0.
  apply: (is_alpha_set_equiv _ _ _ (symmetry (quot_solve_left_drop_zero S1 S0))).
  apply: (interval_quot_solve_dividend_pos_alpha_complete l1 h1 i0 _ S0) => //.
  by exists c; unfold_set.
Qed.

Lemma interval_quot_solve_dividend_neg_nonzero_alpha_complete
    (l1 : WithTop.with_top Z) (h1 : Z) (i0 : interval) (S1 S0 : ℘ Z) :
  h1 < 0 -> (exists c, c ∈ S1 /\ c <> 0) -> (exists c, c ∈ S0) ->
  IsAlpha (A:=itv) (l1, WithTop.NotTop h1) {[ c1 | c1 ∈ S1 /\ c1 <> 0 ]} ->
  IsAlpha (A:=itv) i0 S0 ->
  IsAlpha (A:=itv) (interval_quot_solve_dividend (l1, WithTop.NotTop h1) i0)
    (collecting_quot_solve_left S1 S0).

Proof.
  move=> Hh1 [c [Hc Hc0]] Hex0 Ha1 Ha0.
  apply: (is_alpha_set_equiv _ _ _ (symmetry (quot_solve_left_drop_zero S1 S0))).
  apply: (interval_quot_solve_dividend_neg_alpha_complete l1 h1 i0 _ S0) => //.
  by exists c; unfold_set.
Qed.

(** The γ-level reading, for a user who does not need arbitrary operand sets: on
    a sign-definite divisor the computed interval *is* the hull of the dividend
    solve set. *)
Theorem interval_quot_solve_dividend_pos_best (l1 : Z) (h1 : WithTop.with_top Z)
    (i0 : interval) :
  0 < l1 -> non_bottom (WithTop.NotTop l1, h1) -> non_bottom i0 ->
  BestAbstraction (A:=itv) (interval_quot_solve_dividend (WithTop.NotTop l1, h1) i0)
    (collecting_quot_solve_left (γ[itv] (WithTop.NotTop l1, h1)) (γ[itv] i0)).

Proof.
  move=> Hl1 Hnb1 Hnb0.
  have MR1 := non_bottom_MaximallyReduced _ Hnb1.
  have MR0 := non_bottom_MaximallyReduced _ Hnb0.
  have /non_bottom_non_empty Hex1 := Hnb1.
  have /non_bottom_non_empty Hex0 := Hnb0.
  exact: (binary_alpha_complete_to_best itv itv itv interval_quot_solve_dividend
    _ _ _ (interval_quot_solve_dividend_pos_alpha_complete l1 h1 i0 _ _ Hl1 Hex1 Hex0)).
Qed.

Theorem interval_quot_solve_dividend_neg_best (l1 : WithTop.with_top Z) (h1 : Z)
    (i0 : interval) :
  h1 < 0 -> non_bottom (l1, WithTop.NotTop h1) -> non_bottom i0 ->
  BestAbstraction (A:=itv) (interval_quot_solve_dividend (l1, WithTop.NotTop h1) i0)
    (collecting_quot_solve_left (γ[itv] (l1, WithTop.NotTop h1)) (γ[itv] i0)).

Proof.
  move=> Hh1 Hnb1 Hnb0.
  have MR1 := non_bottom_MaximallyReduced _ Hnb1.
  have MR0 := non_bottom_MaximallyReduced _ Hnb0.
  have /non_bottom_non_empty Hex1 := Hnb1.
  have /non_bottom_non_empty Hex0 := Hnb0.
  exact: (binary_alpha_complete_to_best itv itv itv interval_quot_solve_dividend
    _ _ _ (interval_quot_solve_dividend_neg_alpha_complete l1 h1 i0 _ _ Hh1 Hex1 Hex0)).
Qed.

(** * Divisors that cross zero: split, solve twice, join.

    A sign-definite divisor is settled above; one that crosses zero cannot be,
    and not for want of a better proof.  The largest product wants the divisor
    of one sign and the largest remainder the other, so no single divisor
    realises both and [interval_quot_solve_dividend] is genuinely too wide
    there: [[-3,2]] against [[1,100]] gives [[-302,202]] where the hull of the
    solve set is [[-302,201]].  What *is* exact is the join of the two sign
    halves.

    The lemma below takes those halves as **hypotheses**.  Which divisors
    nearest zero a set contains is a property of the abstraction, not of
    division: an interval can only claim ∓1, a congruence names the divisors
    that are really there.  That is what makes this the entry point for a richer
    domain, exactly as [interval_quot_pos_across_split_alpha_complete]
    ([QuotTheory.v]) is on the forward side.

    Both halves must be inhabited.  [itv] has no ⊑-least element, so no interval
    is α for ∅, and [interval_quot_solve_dividend] does not answer bottom on an
    empty half — which is why the two sign-definite theorems above stay the
    one-sided entry points.
 *)

Lemma interval_quot_solve_dividend_across_split_alpha_complete
    (l1n : WithTop.with_top Z) (h1n : Z) (l1p : Z) (h1p : WithTop.with_top Z)
    (i0 : interval) (S1 S0 : ℘ Z) :
  h1n < 0 -> 0 < l1p ->
  (exists c, c ∈ S1 /\ c < 0) -> (exists c, c ∈ S1 /\ 0 < c) ->
  (exists c, c ∈ S0) ->
  IsAlpha (A:=itv) (l1n, WithTop.NotTop h1n) {[ c1 | c1 ∈ S1 /\ c1 < 0 ]} ->
  IsAlpha (A:=itv) (WithTop.NotTop l1p, h1p) {[ c1 | c1 ∈ S1 /\ 0 < c1 ]} ->
  IsAlpha (A:=itv) i0 S0 ->
  IsAlpha (A:=itv)
    (ZInterval.join (interval_quot_solve_dividend (l1n, WithTop.NotTop h1n) i0)
       (interval_quot_solve_dividend (WithTop.NotTop l1p, h1p) i0))
    (collecting_quot_solve_left S1 S0).

Proof.
  move=> Hh1n Hl1p [cn [HcnS Hcn]] [cp [HcpS Hcp]] Hex0 Han Hap Ha0.
  have Hexn : exists c, c ∈ {[ c1 | c1 ∈ S1 /\ c1 < 0 ]}
    by exists cn; unfold_set; split.
  have Hexp : exists c, c ∈ {[ c1 | c1 ∈ S1 /\ 0 < c1 ]}
    by exists cp; unfold_set; split.
  have Hn := interval_quot_solve_dividend_neg_alpha_complete
    l1n h1n i0 _ S0 Hh1n Hexn Hex0 Han Ha0.
  have Hp := interval_quot_solve_dividend_pos_alpha_complete
    l1p h1p i0 _ S0 Hl1p Hexp Hex0 Hap Ha0.
  apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp).
  exact: (collecting_non_zero_solve_left_split_sign Z.quot S1 S0).
Qed.

(** ** The split-and-join solver.

    [interval_quot_solve_dividend_split] dispatches on [classify]: the two two
    sign-definite answers clamp the divisor's inner bound off zero, and a strict
    straddle takes both halves and joins.  Its theorems are the ones above,
    transported across the branch the classification selects.
 *)

(** On a strict straddle the clamps hit ∓1 exactly, so the two halves are the
    ones the across theorems are stated about. *)
Lemma itv_strictly_negative_part_across (l h : WithTop.with_top Z) :
  high_pos h -> ZInterval.itv_strictly_negative_part (l, h) = (l, WithTop.NotTop (-1)).

Proof.
  move=> Hh.
  rewrite /ZInterval.itv_strictly_negative_part /ZInterval.clamp_upper_bound /=.
  move: Hh; case: h => [|b] Hh //=; simpl in Hh.
  by have -> : Z.min b (-1) = -1 by lia.
Qed.

Lemma itv_strictly_positive_part_across (l h : WithTop.with_top Z) :
  low_neg l -> ZInterval.itv_strictly_positive_part (l, h) = (WithTop.NotTop 1, h).

Proof.
  move=> Hl.
  rewrite /ZInterval.itv_strictly_positive_part /ZInterval.clamp_lower_bound /=.
  move: Hl; case: l => [|a] Hl //=; simpl in Hl.
  by have -> : Z.max a 1 = 1 by lia.
Qed.

(** On a sign-definite divisor the clamp moves a [0] bound off zero and leaves
    every other bound alone, so the half is strictly signed and its γ is exactly
    the non-zero part of the divisor's — which is all the guard admits.  Both
    facts are what [interval_quot_solve_dividend_{pos,neg}_nonzero_alpha_complete]
    ask of their sanitized input. *)
Lemma itv_strictly_positive_part_low (i1 : interval) :
  classify i1 = Pos ->
  exists l1', ZInterval.itv_strictly_positive_part i1 = (WithTop.NotTop l1', snd i1)
    /\ 0 < l1'.

Proof.
  move: i1 => [l h] E.
  have [l' [-> Hl']] := classify_Pos_inv l h E.
  exists (Z.max l' 1).
  rewrite /ZInterval.itv_strictly_positive_part /ZInterval.clamp_lower_bound /=.
  split=> //.
  lia.
Qed.

Lemma itv_strictly_negative_part_high (i1 : interval) :
  classify i1 = Neg ->
  exists h1', ZInterval.itv_strictly_negative_part i1 = (fst i1, WithTop.NotTop h1')
    /\ h1' < 0.

Proof.
  move: i1 => [l h] E.
  have [h' [-> Hh']] := classify_Neg_inv l h E.
  exists (Z.min h' (-1)).
  rewrite /ZInterval.itv_strictly_negative_part /ZInterval.clamp_upper_bound /=.
  split=> //.
  lia.
Qed.

Lemma gamma_itv_strictly_positive_part (i1 : interval) :
  classify i1 = Pos ->
  γ[itv] (ZInterval.itv_strictly_positive_part i1) ⊆⊇
  {[ c | c ∈ γ[itv] i1 /\ c <> 0 ]}.

Proof.
  move: i1 => [l h] E.
  have [l' [-> Hl']] := classify_Pos_inv l h E.
  clear E.
  rewrite /ZInterval.itv_strictly_positive_part /ZInterval.clamp_lower_bound /=.
  split=> z; case: h => [|b]; unfold_set; simpl in *; move=> *; repeat split; lia.
Qed.

Lemma gamma_itv_strictly_negative_part (i1 : interval) :
  classify i1 = Neg ->
  γ[itv] (ZInterval.itv_strictly_negative_part i1) ⊆⊇
  {[ c | c ∈ γ[itv] i1 /\ c <> 0 ]}.

Proof.
  move: i1 => [l h] E.
  have [h' [-> Hh']] := classify_Neg_inv l h E.
  clear E.
  rewrite /ZInterval.itv_strictly_negative_part /ZInterval.clamp_upper_bound /=.
  split=> z; case: l => [|a]; unfold_set; simpl in *; move=> *; repeat split; lia.
Qed.

(** Restricting the divisor set to any set with the same non-zero part is a
    no-op on the solve set: the guard has already discarded the rest.  The
    two-sided [quot_solve_left_drop_zero], and what lets a clamped divisor stand
    in for the original. *)
Lemma quot_solve_left_restrict_nonzero (S1 S1' S0 : ℘ Z) :
  S1' ⊆⊇ {[ c | c ∈ S1 /\ c <> 0 ]} ->
  collecting_quot_solve_left S1 S0 ⊆⊇ collecting_quot_solve_left S1' S0.

Proof.
  move=> [Hsub Hsup].
  apply: collecting_binary_solve_left_partial_restrict.
  - move=> c /Hsub; unfold_set; by move=> [].
  - move=> c2 c1 Hc1 Hne.
    apply: Hsup.
    by unfold_set.
Qed.

Lemma interval_quot_solve_dividend_split_sound (i1 i0 : interval) :
  Overapproximates (A:=itv) (interval_quot_solve_dividend_split i1 i0)
    (collecting_quot_solve_left (γ[itv] i1) (γ[itv] i0)).

Proof.
  move: i1 => [l h]; rewrite /interval_quot_solve_dividend_split.
  case E: (classify (l, h)).
  - rewrite /Overapproximates (quot_solve_left_restrict_nonzero _ _ (γ[itv] i0)
      (gamma_itv_strictly_positive_part (l, h) E)).
    exact: interval_quot_solve_dividend_sound.
  - rewrite /Overapproximates (quot_solve_left_restrict_nonzero _ _ (γ[itv] i0)
      (gamma_itv_strictly_negative_part (l, h) E)).
    exact: interval_quot_solve_dividend_sound.
  - have [Hl Hh] := classify_Across_signs l h E.
    rewrite (itv_strictly_negative_part_across l h Hh)
      (itv_strictly_positive_part_across l h Hl).
    have Hn := gamma_itv_neg_half l h Hh.
    have Hp := gamma_itv_pos_half l h Hl.
    have Hcover : forall c2 c1 : Z, c1 ∈ γ[itv] (l, h) -> is_nonzero c2 c1 ->
        c1 ∈ γ[itv] (l, WithTop.NotTop (-1)) \/ c1 ∈ γ[itv] (WithTop.NotTop 1, h).
    { move=> c2 c1 Hc1; rewrite /is_nonzero => Hne.
      case: (Z.le_gt_cases c1 0) => Hs.
      - left.
        apply: (proj2 Hn); unfold_set; split=> //; lia.
      - right.
        apply: (proj2 Hp); unfold_set; split=> //; lia.
    } have Hsa : γ[itv] (l, WithTop.NotTop (-1)) ⊆ γ[itv] (l, h)
        by move=> z /(proj1 Hn); unfold_set; by move=> [].
    have Hsb : γ[itv] (WithTop.NotTop 1, h) ⊆ γ[itv] (l, h)
      by move=> z /(proj1 Hp); unfold_set; by move=> [].
    (* The generic split is stated on the unnamed form, so unfold before it. *)
    rewrite /Overapproximates /collecting_quot_solve_left
      (collecting_binary_solve_left_partial_split is_nonzero Z.quot (γ[itv] (l, h))
        (γ[itv] (l, WithTop.NotTop (-1))) (γ[itv] (WithTop.NotTop 1, h))
        (γ[itv] i0) Hcover Hsa Hsb).
    transitivity (γ[itv] (interval_quot_solve_dividend (l, WithTop.NotTop (-1)) i0)
      ∪ γ[itv] (interval_quot_solve_dividend (WithTop.NotTop 1, h) i0));
      last exact: join_sound.
    apply: propset_union_mono; exact: interval_quot_solve_dividend_sound.
Qed.

Lemma interval_quot_solve_dividend_split_pos_alpha_complete (l1 : Z)
    (h1 : WithTop.with_top Z) (i0 : interval) (S1 S0 : ℘ Z) :
  0 < l1 -> (exists c, c ∈ S1) -> (exists c, c ∈ S0) ->
  binary_alpha_complete itv itv itv interval_quot_solve_dividend_split
    collecting_quot_solve_left (WithTop.NotTop l1, h1) i0 S1 S0.

Proof.
  rewrite /binary_alpha_complete => Hl1 Hex1 Hex0 Ha1 Ha0.
  rewrite /interval_quot_solve_dividend_split (classify_pos_of_low l1 h1 Hl1)
    /ZInterval.itv_strictly_positive_part /ZInterval.clamp_lower_bound /=.
  have Hmax : Z.max l1 1 = l1 by lia.
  rewrite Hmax.
  exact: (interval_quot_solve_dividend_pos_alpha_complete l1 h1 i0 S1 S0 Hl1
    Hex1 Hex0 Ha1 Ha0).
Qed.

Lemma interval_quot_solve_dividend_split_neg_alpha_complete
    (l1 : WithTop.with_top Z) (h1 : Z) (i0 : interval) (S1 S0 : ℘ Z) :
  h1 < 0 -> (exists c, c ∈ S1) -> (exists c, c ∈ S0) ->
  binary_alpha_complete itv itv itv interval_quot_solve_dividend_split
    collecting_quot_solve_left (l1, WithTop.NotTop h1) i0 S1 S0.

Proof.
  rewrite /binary_alpha_complete => Hh1 Hex1 Hex0 Ha1 Ha0.
  have Hnb1 : non_bottom (l1, WithTop.NotTop h1)
    by move: Hex1 => [c Hc]; exact: non_bottom_of_alpha Ha1 Hc.
  rewrite /interval_quot_solve_dividend_split (classify_neg_of_high l1 h1 Hh1 Hnb1)
    /ZInterval.itv_strictly_negative_part /ZInterval.clamp_upper_bound /=.
  have Hmin : Z.min h1 (-1) = h1 by lia.
  rewrite Hmin.
  exact: (interval_quot_solve_dividend_neg_alpha_complete l1 h1 i0 S1 S0 Hh1
    Hex1 Hex0 Ha1 Ha0).
Qed.

(** ** Absorption: the join does not depend on where the divisor is split.

    The ∓1 halves an interval can name are not α of an arbitrary [S1]'s sign
    halves — [S1 = {-4,4}] has negative half [{-4}], whose α is [[-4,-4]], not
    [[-4,-1]] — so the lemma above does not directly give α-completeness for the
    ∓1 form.  What closes the gap is that the joined value does not depend on
    the split point at all: each half invents an inner bound, and the join
    swallows it against the other half's outer bound.  So the split can be taken
    at the *true* extremal divisors of [S1], which
    [itv_split_at_zero_strict_alpha] produces, and transported to ∓1.

    This is the same manoeuvre as [interval_mul_pos_across_join_eq]
    ([MulTheory.v]) on the forward side, and for the same reason: the abstract
    value does not mention the split point, so it need not know it.  It is also
    exactly where forward *quot* cannot follow — there the extremes sit at the
    divisors nearest zero, so no absorption exists and α-completeness is
    genuinely false ([quot_across_no_alpha_complete]).

    Two cases carry it.  When [0 ∈ γ i0] the inner bound of each product is
    multiplied by a bound of [i0] that is [0] (or [i0] crosses zero, and the
    product does not read the inner bound at all), so the products are equal
    outright.  When [i0] excludes [0] the inner bound survives but carries the
    sign opposite to the other half's outer bound, and [min]/[max] discards it.
 *)

(** A sign half's outer bound has the sign its type claims.  Standalone because
    [case: l] cannot run once a derived hypothesis mentions [l]; with these,
    [across_{neg,pos}_half_non_bottom] ([ZIntervalTheory.v]) supplies the ∓1
    caps. *)
Lemma across_low_neg_of_half (l : WithTop.with_top Z) (m : Z) :
  m < 0 -> non_bottom (l, WithTop.NotTop m) -> low_neg l.

Proof.
  move=> Hm; case: l => [|a] Hnb; [exact I | simpl in Hnb; simpl; lia].
Qed.

Lemma across_high_pos_of_half (p : Z) (h : WithTop.with_top Z) :
  0 < p -> non_bottom (WithTop.NotTop p, h) -> high_pos h.

Proof.
  move=> Hp; case: h => [|b] Hnb; [exact I | simpl in Hnb; simpl; lia].
Qed.

(** An interval that misses [0] is strictly of one sign. *)
Lemma itv_gammab_zero_false_sign (i0 : interval) :
  itv_gammab i0 0 = false -> low_pos (fst i0) \/ high_neg (snd i0).

Proof.
  move: i0 => [l0 h0]; rewrite /itv_gammab /glb_gammab /lub_gammab /=.
  case: l0 => [|a]; case: h0 => [|b] //=; bcase.
Qed.

(** [itv_max_abs] of a sign half is its *outer* bound: [l <= m < 0] makes [|l|]
    the larger, whatever [m] is.  Hence the window is common to all splits, ∓1
    included. *)
Lemma quot_remainder_window_sym_neg_half_eq (l : WithTop.with_top Z) (m : Z) :
  m < 0 -> non_bottom (l, WithTop.NotTop m) ->
  quot_remainder_window_sym (l, WithTop.NotTop m) =
  quot_remainder_window_sym (l, WithTop.NotTop (-1)).

Proof.
  move=> Hm Hnb.
  rewrite !quot_remainder_window_sym_eq /itv_max_abs.
  case: l Hnb => [|a] Hnb //.
  simpl in Hnb.
  f_equal.
  lia.
Qed.

Lemma quot_remainder_window_sym_pos_half_eq (p : Z) (h : WithTop.with_top Z) :
  0 < p -> non_bottom (WithTop.NotTop p, h) ->
  quot_remainder_window_sym (WithTop.NotTop p, h) =
  quot_remainder_window_sym (WithTop.NotTop 1, h).

Proof.
  move=> Hp Hnb.
  rewrite !quot_remainder_window_sym_eq /itv_max_abs.
  case: h Hnb => [|b] Hnb //.
  simpl in Hnb.
  f_equal.
  lia.
Qed.

(** The product's sign class is fixed by the two operands' classes, which both
    splits share, so the clamp is common too. *)
Lemma quot_remainder_window_neg_half_eq (l : WithTop.with_top Z) (m : Z)
    (i0 : interval) :
  m < 0 -> non_bottom (l, WithTop.NotTop m) -> non_bottom i0 ->
  quot_remainder_window (interval_mul i0 (l, WithTop.NotTop m))
    (l, WithTop.NotTop m) i0 =
  quot_remainder_window (interval_mul i0 (l, WithTop.NotTop (-1)))
    (l, WithTop.NotTop (-1)) i0.

Proof.
  move=> Hm Hnb Hnb0.
  have Hnb' := across_neg_half_non_bottom l (across_low_neg_of_half l m Hm Hnb).
  rewrite /quot_remainder_window (quot_remainder_window_sym_neg_half_eq l m Hm Hnb).
  case E: (itv_gammab i0 0) => //.
  case: (itv_gammab_zero_false_sign i0 E) => Hs.
  - move: i0 Hnb0 E Hs => [[|l0] h0] Hnb0 E Hs; first by case: Hs.
    simpl in Hs.
    by rewrite (classify_mul_neg_pos l m l0 h0 Hm Hs Hnb Hnb0)
      (classify_mul_neg_pos l (-1) l0 h0 (ltac:(lia)) Hs Hnb' Hnb0).
  - move: i0 Hnb0 E Hs => [l0 [|h0]] Hnb0 E Hs; first by case: Hs.
    simpl in Hs.
    have Hc0 := classify_neg_of_high l0 h0 Hs Hnb0.
    by rewrite (classify_mul_neg_neg l m _ Hm Hnb Hnb0 Hc0)
      (classify_mul_neg_neg l (-1) _ (ltac:(lia)) Hnb' Hnb0 Hc0).
Qed.

Lemma quot_remainder_window_pos_half_eq (p : Z) (h : WithTop.with_top Z)
    (i0 : interval) :
  0 < p -> non_bottom (WithTop.NotTop p, h) -> non_bottom i0 ->
  quot_remainder_window (interval_mul i0 (WithTop.NotTop p, h))
    (WithTop.NotTop p, h) i0 =
  quot_remainder_window (interval_mul i0 (WithTop.NotTop 1, h))
    (WithTop.NotTop 1, h) i0.

Proof.
  move=> Hp Hnb Hnb0.
  have Hnb' := across_pos_half_non_bottom h (across_high_pos_of_half p h Hp Hnb).
  rewrite /quot_remainder_window (quot_remainder_window_sym_pos_half_eq p h Hp Hnb).
  case E: (itv_gammab i0 0) => //.
  case: (itv_gammab_zero_false_sign i0 E) => Hs.
  - move: i0 Hnb0 E Hs => [[|l0] h0] Hnb0 E Hs; first by case: Hs.
    simpl in Hs.
    have Hc0 := classify_pos_of_low l0 h0 Hs.
    by rewrite (classify_mul_pos_pos p h _ Hp Hc0)
      (classify_mul_pos_pos 1 h _ (ltac:(lia)) Hc0).
  - move: i0 Hnb0 E Hs => [l0 [|h0]] Hnb0 E Hs; first by case: Hs.
    simpl in Hs.
    have Hc0 := classify_neg_of_high l0 h0 Hs Hnb0.
    by rewrite (classify_mul_pos_neg p h _ Hp Hnb Hnb0 Hc0)
      (classify_mul_pos_neg 1 h _ (ltac:(lia)) Hnb' Hnb0 Hc0).
Qed.

(** The two products, when [0 ∈ γ i0]: the inner bound is multiplied by a zero
    bound of [i0], or [i0] crosses zero and the product ignores it. *)
Lemma interval_mul_neg_half_eq_zero (l : WithTop.with_top Z) (m : Z)
    (i0 : interval) :
  m < 0 -> non_bottom (l, WithTop.NotTop m) -> non_bottom i0 ->
  itv_gammab i0 0 = true ->
  interval_mul i0 (l, WithTop.NotTop m) = interval_mul i0 (l, WithTop.NotTop (-1)).

Proof.
  move=> Hm Hnb Hnb0 E.
  have Hnb' := across_neg_half_non_bottom l (across_low_neg_of_half l m Hm Hnb).
  rewrite /interval_mul (classify_neg_of_high l m Hm Hnb)
    (classify_neg_of_high l (-1) (ltac:(lia)) Hnb').
  move: i0 Hnb0 E => [l0 h0] Hnb0 E.
  rewrite /itv_gammab /glb_gammab /lub_gammab /classify /bound_mul in E Hnb0 *.
  case: l0 E Hnb0 => [|c] E Hnb0;
    case: h0 E Hnb0 => [|d] E Hnb0;
    case: l Hnb Hnb' => [|a] Hnb Hnb'; bcase.
Qed.

Lemma interval_mul_pos_half_eq_zero (p : Z) (h : WithTop.with_top Z)
    (i0 : interval) :
  0 < p -> non_bottom (WithTop.NotTop p, h) -> non_bottom i0 ->
  itv_gammab i0 0 = true ->
  interval_mul i0 (WithTop.NotTop p, h) = interval_mul i0 (WithTop.NotTop 1, h).

Proof.
  move=> Hp Hnb Hnb0 E.
  rewrite /interval_mul (classify_pos_of_low p h Hp)
    (classify_pos_of_low 1 h (ltac:(lia))).
  move: i0 Hnb0 E => [l0 h0] Hnb0 E.
  rewrite /itv_gammab /glb_gammab /lub_gammab /classify /bound_mul in E Hnb0 *.
  case: l0 E Hnb0 => [|c] E Hnb0;
    case: h0 E Hnb0 => [|d] E Hnb0;
    case: h Hnb => [|b] Hnb; bcase.
Qed.

(** The absorption itself.
 *)
Lemma interval_quot_solve_dividend_split_join_eq
    (l h : WithTop.with_top Z) (m p : Z) (i0 : interval) :
  m < 0 -> 0 < p ->
  non_bottom (l, WithTop.NotTop m) -> non_bottom (WithTop.NotTop p, h) ->
  non_bottom i0 ->
  ZInterval.join
    (interval_quot_solve_dividend (l, WithTop.NotTop m) i0)
    (interval_quot_solve_dividend (WithTop.NotTop p, h) i0)
  = interval_quot_solve_dividend_split (l, h) i0.

Proof.
  move=> Hm Hp Hnbn Hnbp Hnb0.
  have Hnbn' := across_neg_half_non_bottom l (across_low_neg_of_half l m Hm Hnbn).
  have Hnbp' := across_pos_half_non_bottom h (across_high_pos_of_half p h Hp Hnbp).
  have Hl := across_low_neg_of_half l m Hm Hnbn.
  have Hh := across_high_pos_of_half p h Hp Hnbp.
  rewrite /interval_quot_solve_dividend_split
    (classify_Across_of_signs l h Hl Hh)
    (itv_strictly_negative_part_across l h Hh)
    (itv_strictly_positive_part_across l h Hl) /=.
  rewrite /interval_quot_solve_dividend
    (quot_remainder_window_neg_half_eq l m i0 Hm Hnbn Hnb0)
    (quot_remainder_window_pos_half_eq p h i0 Hp Hnbp Hnb0).
  case E: (itv_gammab i0 0).
  - by rewrite (interval_mul_neg_half_eq_zero l m i0 Hm Hnbn Hnb0 E)
      (interval_mul_pos_half_eq_zero p h i0 Hp Hnbp Hnb0 E).
  - rewrite /quot_remainder_window E quot_remainder_window_sym_eq /itv_sym
      /itv_max_abs.
    case: (itv_gammab_zero_false_sign i0 E) => Hs.
    + move: i0 Hnb0 E Hs => [[|l0] h0] Hnb0 E Hs; first by case: Hs.
      simpl in Hs.
      have Hc0 := classify_pos_of_low l0 h0 Hs.
      rewrite (classify_mul_neg_pos l (-1) l0 h0 (ltac:(lia)) Hs Hnbn' Hnb0)
        (classify_mul_pos_pos 1 h _ (ltac:(lia)) Hc0)
        /interval_mul
        (classify_neg_of_high l (-1) (ltac:(lia)) Hnbn')
        (classify_pos_of_low 1 h (ltac:(lia)))
        (classify_neg_of_high l m Hm Hnbn)
        (classify_pos_of_low p h Hp) Hc0.
      rewrite /ZInterval.join /ZInterval.join_lb /ZInterval.join_ub
        /interval_add /bound_mul /WithTop.lift2.
      move: Hnbn Hnbn' Hl Hnbp Hnbp' Hh E Hnb0 Hc0 Hs.
      case: l => [|a];
        case: h => [|b];
        case: h0 => [|d];
        case: l0 => [|q|q];
        move=> *; bcase; congr pair; try congr WithTop.NotTop; bcase.
    + move: i0 Hnb0 E Hs => [l0 [|h0]] Hnb0 E Hs; first by case: Hs.
      simpl in Hs.
      have Hc0 := classify_neg_of_high l0 h0 Hs Hnb0.
      rewrite (classify_mul_neg_neg l (-1) _ (ltac:(lia)) Hnbn' Hnb0 Hc0)
        (classify_mul_pos_neg 1 h _ (ltac:(lia)) Hnbp' Hnb0 Hc0)
        /interval_mul
        (classify_neg_of_high l (-1) (ltac:(lia)) Hnbn')
        (classify_pos_of_low 1 h (ltac:(lia)))
        (classify_neg_of_high l m Hm Hnbn)
        (classify_pos_of_low p h Hp) Hc0.
      rewrite /ZInterval.join /ZInterval.join_lb /ZInterval.join_ub
        /interval_add /bound_mul /WithTop.lift2.
      move: Hnbn Hnbn' Hl Hnbp Hnbp' Hh E Hnb0 Hc0 Hs.
      case: l => [|a];
        case: h => [|b];
        case: l0 => [|c];
        case: h0 => [|e|e];
        move=> *; bcase; congr pair; try congr WithTop.NotTop; bcase.
Qed.


(**
    α-complete, for arbitrary operand sets, at the ∓1 halves the transfer
    function actually computes: split [S1] at its own extremal divisors
    ([itv_split_at_zero_strict_alpha]), apply the lemma above there, and
    transport across the absorption. This is the statement the brute force
    over subsets of [[-4,4]] measured, and the one a product domain can rely
    on: no congruence or known-bits refinement of a zero-crossing divisor
    sharpens the interval this returns.

    Without the split it is genuinely loose here — [[-3,2]] against [[1,100]]
    gives [[-302,202]] where the hull is [[-302,201]]. And the transport is
    the same manoeuvre [interval_mul_pos_across_abstract] makes on the forward
    side, the one forward *quot* cannot make at all
    ([quot_across_no_alpha_complete]).
 *)
Lemma interval_quot_solve_dividend_split_across_alpha_complete
    (l h : WithTop.with_top Z) (i0 : interval) (S1 S0 : ℘ Z) :
  low_neg l -> high_pos h -> (exists c, c ∈ S1) -> (exists c, c ∈ S0) ->
  binary_alpha_complete itv itv itv interval_quot_solve_dividend_split
    collecting_quot_solve_left (l, h) i0 S1 S0.

Proof.
  rewrite /binary_alpha_complete => Hl Hh Hex1 Hex0 Ha1 Ha0.
  have Hnb0 : non_bottom i0 by move: Hex0 => [c Hc]; exact: non_bottom_of_alpha Ha0 Hc.
  apply: (itv_split_at_zero_strict_alpha l h S1 Hl Hh Hex1 Ha1) => m p HmS Hm HpS Hp Han Hap.
  have Hmemn : m ∈ {[ z | z ∈ S1 /\ z < 0 ]} by unfold_set; split.
  have Hmemp : p ∈ {[ z | z ∈ S1 /\ 0 < z ]} by unfold_set; split.
  have Hnbn := non_bottom_of_alpha _ _ _ Han Hmemn.
  have Hnbp := non_bottom_of_alpha _ _ _ Hap Hmemp.
  rewrite -(interval_quot_solve_dividend_split_join_eq l h m p i0 Hm Hp Hnbn Hnbp Hnb0).
  apply: (interval_quot_solve_dividend_across_split_alpha_complete l m p h i0 S1 S0) => //;
    by [exists m | exists p].
Qed.

(**
    ** Bestness on every divisor that has a legal value.

    One theorem for all three branches, and the reason the clamp is worth
    having: on *any* divisor interval containing a non-zero integer, the split
    solver returns the hull of the dividend solve set. The quotient set [S0]
    stays arbitrary; only the divisor is pinned to a concretization, hence
    [_best].

    The hypothesis is necessary rather than convenient. A divisor of exactly
    [{0}] leaves the solve set empty, and no interval is α of ∅ — [itv] has no
    ⊑-least element, since it represents ∅ many ways and is not [ExactOrder].
    Soundness still covers that case
    ([interval_quot_solve_dividend_split_sound]).

    α-completeness holds in the two sign-definite branches and across zero
    ([interval_quot_solve_dividend_split_{pos,neg,across}_alpha_complete]) but
    *not* in the clamped 0-on-a-bound case, and that is not an artefact: the
    clamp claims a divisor ∓1, and an operand set need not contain it — [S1 =
    {-4,0}] against [S0 = {-4}] has solve hull [[16,19]] where the interval,
    having only [[-4,-1]] to work with, must say [[4,19]]. Removing a zero
    more sharply than to ∓1 is a property of the abstraction, which is why the
    α-complete statements take the split as input.
 *)
Theorem interval_quot_solve_dividend_split_best (i1 i0 : interval) (S0 : ℘ Z) :
  (exists c, c ∈ γ[itv] i1 /\ c <> 0) -> (exists c, c ∈ S0) ->
  IsAlpha (A:=itv) i0 S0 ->
  IsAlpha (A:=itv) (interval_quot_solve_dividend_split i1 i0)
    (collecting_quot_solve_left (γ[itv] i1) S0).

Proof.
  move=> Hex1 Hex0 Ha0.
  move: i1 Hex1 => [l h] Hex1.
  case E: (classify (l, h)).
  - rewrite /interval_quot_solve_dividend_split E.
    have [l' [Hhalf Hl']] := itv_strictly_positive_part_low (l, h) E.
    have Heq := gamma_itv_strictly_positive_part (l, h) E.
    have Hnbh : non_bottom (ZInterval.itv_strictly_positive_part (l, h)).
    { apply/non_bottom_non_empty.
      move: Hex1 => [c [Hc Hne]].
      exists c.
      by apply: (proj2 Heq); unfold_set.
    } rewrite Hhalf; rewrite Hhalf in Heq Hnbh.
    apply: (interval_quot_solve_dividend_pos_nonzero_alpha_complete l' (snd (l, h)) i0
      (γ[itv] (l, h)) S0 Hl' Hex1 Hex0) => //.
    exact: (is_alpha_set_equiv _ _ _ Heq (non_bottom_is_alpha_gamma _ Hnbh)).
  - rewrite /interval_quot_solve_dividend_split E.
    have [h' [Hhalf Hh']] := itv_strictly_negative_part_high (l, h) E.
    have Heq := gamma_itv_strictly_negative_part (l, h) E.
    have Hnbh : non_bottom (ZInterval.itv_strictly_negative_part (l, h)).
    { apply/non_bottom_non_empty.
      move: Hex1 => [c [Hc Hne]].
      exists c.
      by apply: (proj2 Heq); unfold_set.
    } rewrite Hhalf; rewrite Hhalf in Heq Hnbh.
    apply: (interval_quot_solve_dividend_neg_nonzero_alpha_complete (fst (l, h)) h' i0
      (γ[itv] (l, h)) S0 Hh' Hex1 Hex0) => //.
    exact: (is_alpha_set_equiv _ _ _ Heq (non_bottom_is_alpha_gamma _ Hnbh)).
  - have [Hl Hh] := classify_Across_signs l h E.
    have Hnb := across_non_bottom (l, h) Hl Hh.
    have /non_bottom_non_empty Hex1' := Hnb.
    exact: (interval_quot_solve_dividend_split_across_alpha_complete l h i0 (γ[itv] (l, h))
      S0 Hl Hh Hex1' Hex0 (non_bottom_is_alpha_gamma _ Hnb) Ha0).
Qed.

(**
    The dividend's transfer function is *not* [refine_by i2] of the solve set
    above — see [ZIntervalBackwardOps.v] — so its results live after the
    divisor's, below, which is what they are built on.
 *)


(**
    * Refining the divisor — solve per sign half, meet inside, join.

    This is the one backward step in the file that is not a widening of a
    solve set but the solve set itself, and the reason is a convexity fact the
    dividend does not have: once the divisor's *sign* is fixed, the compatible
    divisors form an interval, with no holes.

    Write [m(b)] and [M(b)] for the least and the greatest dividend whose
    quotient by [b > 0] lands in [γ i0] — the two ends of
    [interval_quot_solve_dividend (b,b) i0], the previous section's solve step
    at a single divisor. A divisor [b] is compatible exactly when [γ i2] meets
    [[m(b), M(b)]], i.e. when [m(b) ≤ h2] and [l2 ≤ M(b)]; both are affine in
    [b], so each conjunct cuts a half-line out of [b ≥ 1].

    Which half-line it cuts is the antitony of division: a *lower* bound on
    the quotient caps the divisor, an *upper* bound puts a floor under it. The
    four lemmas below are the four (conjunct, sign) pairs, and each is an
    adjunction — a bound on the quotient on one side, a bound on the divisor
    on the other, exchanged by a division.

    Both halves meet the incoming [i1] *before* the join, which is not a
    stylistic choice: meeting afterwards re-admits the points between the two
    halves. See [todo/quot_backward_divisor.md] for the measurements.
 *)

(**
    ** The quotient window, as two biconditionals on [Z].

    At a fixed divisor [b > 0], the dividends whose quotient clears a given
    bound are exactly those clearing a bound of their own.

    That set is an interval with no holes, which is §1's central fact and the
    reason the divisor's solve set is convex on each sign half. It is proved
    here directly, as two biconditionals on [Z], rather than by identifying it
    with [interval_quot_solve_dividend (b,b) i0]: the two [Z] facts are
    shorter than unfolding [interval_mul] and [quot_remainder_window] at a
    singleton divisor, and they are reusable — the four adjunctions below are
    the same pair of lemmas applied to the *other* division.
 *)

Lemma quot_ge_iff_pos (b z c2 : Z) : 0 < b -> 0 < z -> (z <= Z.quot c2 b <-> z * b <= c2).

Proof.
  move=> Hb Hz.
  split=> H.
  - have Hc2 : 0 <= c2.
    { case: (Z.le_gt_cases 0 c2) => // Hneg.
      have : Z.quot c2 b <= 0 by apply: Z.quot_le_upper_bound; lia.
      lia.
    } have [_ Hmq] := Z.mul_quot_le c2 b Hc2 (ltac:(lia) : b <> 0).
    nia.
  - apply: Z.quot_le_lower_bound; nia.
Qed.

(**
    A non-positive quotient bound is reached one step *past* the product,
    because truncation rounds towards zero: [c2 ÷ b ≥ 0] already at [c2 = 1 -
    b].
 *)
Lemma quot_ge_iff_nonpos (b z c2 : Z) :
  0 < b -> z <= 0 -> (z <= Z.quot c2 b <-> (z - 1) * b + 1 <= c2).

Proof.
  move=> Hb Hz.
  split=> H.
  - case: (Z.le_gt_cases c2 ((z - 1) * b)) => Hle; last lia.
    have : Z.quot c2 b <= z - 1 by apply: Z.quot_le_upper_bound; nia.
    lia.
  - case: (Z.le_gt_cases z (Z.quot c2 b)) => // Hlt.
    have Hq : Z.quot c2 b <= z - 1 by lia.
    have Hc2 : c2 <= 0.
    { case: (Z.le_gt_cases c2 0) => // Hpos.
      have : 0 <= Z.quot c2 b by apply: Z.quot_le_lower_bound; lia.
      lia.
    } have [Hmq _] := Z.mul_quot_ge c2 b Hc2 (ltac:(lia) : b <> 0).
    nia.
Qed.

(**
    The high end is the low end of the negated dividend: [Z.quot_opp_l] turns
    each of the two lemmas above into its mirror, so only two of the four
    directions carry arithmetic. Same manoeuvre the sign cases make on the
    forward side ([collecting_quot_opp_l], [QuotTheory.v]).
 *) Lemma quot_le_iff_neg (b z c2 : Z) : 0 < b -> z < 0 -> (Z.quot c2 b <= z <-> c2 <= z * b).

Proof.
  move=> Hb Hz.
  have Hopp : Z.quot (- c2) b = - Z.quot c2 b by rewrite Z.quot_opp_l //; lia.
  have := quot_ge_iff_pos b (- z) (- c2) Hb (ltac:(lia) : 0 < - z).
  rewrite Hopp.
  lia.
Qed.

Lemma quot_le_iff_nonneg (b z c2 : Z) :
  0 < b -> 0 <= z -> (Z.quot c2 b <= z <-> c2 <= (z + 1) * b - 1).

Proof.
  move=> Hb Hz.
  have Hopp : Z.quot (- c2) b = - Z.quot c2 b by rewrite Z.quot_opp_l //; lia.
  have := quot_ge_iff_nonpos b (- z) (- c2) Hb (ltac:(lia) : - z <= 0).
  rewrite Hopp.
  lia.
Qed.

(**
    ** Solving a quotient bound for the divisor.

    Each is one application of a biconditional above to the division
    [quot_bound] performs — the adjunction that exchanges a bound on the
    quotient for a bound on the divisor, which is where the C99 rounding
    enters and why the two lemmas that produce a *lower* bound carry the [+1].
    All four are stated at a single divisor [b > 0]; the negative half is
    obtained by negating the quotient interval, not by mirroring them.
 *)

(**
    A strictly positive quotient bound caps the divisor.
 *)
Lemma quot_divisor_upper_of_qlow (c2 h2 l0 b : Z) :
  0 < b -> 0 < l0 -> l0 <= Z.quot c2 b -> c2 <= h2 -> b <= Z.quot h2 l0.

Proof.
  move=> Hb Hl0 Hq Hh2.
  have Hmq := proj1 (quot_ge_iff_pos b l0 c2 Hb Hl0) Hq.
  apply: Z.quot_le_lower_bound; nia.
Qed.

(**
    A non-positive one puts a floor under it: the dividend cannot be as low as
    [m(b) = b * (l0 - 1) + 1]. Truncation makes the two cases: with a positive
    [h2] the constraint is vacuous, and the computed bound lands at or below
    [1], where the clamp on the divisor absorbs it.
 *)
Lemma quot_divisor_lower_of_qlow (c2 h2 l0 b : Z) :
  0 < b -> l0 <= 0 -> l0 <= Z.quot c2 b -> c2 <= h2 -> Z.quot h2 (l0 - 1) + 1 <= b.

Proof.
  move=> Hb Hl0 Hq Hh2.
  have Hm : b * (l0 - 1) < c2 by have := proj1 (quot_ge_iff_nonpos b l0 c2 Hb Hl0) Hq; nia.
  have Hne : l0 - 1 <> 0 by lia.
  case: (Z.le_gt_cases h2 0) => Hh2s.
  - rewrite -(Z.quot_opp_opp h2 (l0 - 1) Hne).
    suff : Z.quot (- h2) (- (l0 - 1)) < b by lia.
    apply: Z.quot_lt_upper_bound; nia.
  - have : Z.quot h2 (l0 - 1) <= 0; last lia.
    have Hnz : 1 - l0 <> 0 by lia.
    have -> : l0 - 1 = - (1 - l0) by lia.
    rewrite (Z.quot_opp_r h2 (1 - l0) Hnz).
    have : 0 <= Z.quot h2 (1 - l0); last lia.
    apply: Z.quot_le_lower_bound; nia.
Qed.

(**
    The mirror pair, from the high end of the quotient.
 *)
Lemma quot_divisor_upper_of_qhigh (c2 l2 h0 b : Z) :
  0 < b -> h0 < 0 -> Z.quot c2 b <= h0 -> l2 <= c2 -> b <= Z.quot l2 h0.

Proof.
  move=> Hb Hh0 Hq Hl2.
  have Hmq := proj1 (quot_le_iff_neg b h0 c2 Hb Hh0) Hq.
  have Hne : h0 <> 0 by lia.
  rewrite -(Z.quot_opp_opp l2 h0 Hne).
  apply: Z.quot_le_lower_bound; nia.
Qed.

Lemma quot_divisor_lower_of_qhigh (c2 l2 h0 b : Z) :
  0 < b -> 0 <= h0 -> Z.quot c2 b <= h0 -> l2 <= c2 ->
  Z.quot l2 (h0 + 1) + 1 <= b.

Proof.
  move=> Hb Hh0 Hq Hl2.
  have HM : c2 < b * (h0 + 1) by have := proj1 (quot_le_iff_nonneg b h0 c2 Hb Hh0) Hq; nia.
  case: (Z.le_gt_cases 0 l2) => Hl2s.
  - suff : Z.quot l2 (h0 + 1) < b by lia.
    apply: Z.quot_lt_upper_bound; nia.
  - have : Z.quot l2 (h0 + 1) <= 0; last lia.
    apply: Z.quot_le_upper_bound; nia.
Qed.

(**
    ** The dividend window at one divisor.

    The four lemmas above read a compatible [(c2, c0)] off and produce a bound
    on [b]. Bestness needs the other direction — a [b] the transfer function
    returns must be *realised* — so it needs the exact set of dividends that a
    fixed [b] sends into [γ i0]:

    << m(b) = l0*b - (b-1)*[l0 ≤ 0] M(b) = h0*b + (b-1)*[0 ≤ h0] >>

    That set is an interval with no holes, and the biconditionals above are
    exactly it, read one bound at a time.
 *)

(**
    [m(b)] and [M(b)] as bounds. The sign test is [Z_lt_le_dec], the one
    [quot_divisor_pos_q{low,high}] already branches on, so the two case splits
    line up.
 *)
Definition quot_window_low (l0 : WithTop.with_top Z) (b : Z) : WithTop.with_top Z :=
  match l0 with
  | WithTop.Top => WithTop.Top
  | WithTop.NotTop z =>
      WithTop.NotTop (match Z_lt_le_dec 0 z with
                      | left _ => z * b
                      | right _ => (z - 1) * b + 1
                      end)
  end.

Definition quot_window_high (h0 : WithTop.with_top Z) (b : Z) : WithTop.with_top Z :=
  match h0 with
  | WithTop.Top => WithTop.Top
  | WithTop.NotTop z =>
      WithTop.NotTop (match Z_lt_le_dec z 0 with
                      | left _ => z * b
                      | right _ => (z + 1) * b - 1
                      end)
  end.

Definition quot_window (i0 : interval) (b : Z) : interval :=
  (quot_window_low (fst i0) b, quot_window_high (snd i0) b).

(**
    The window is *exactly* the preimage: no holes, hence the convexity the
    divisor side lives on.
 *)
Lemma quot_window_iff (i0 : interval) (b c2 : Z) :
  0 < b -> (Z.quot c2 b ∈ γ[itv] i0 <-> c2 ∈ γ[itv] (quot_window i0 b)).

Proof.
  move=> Hb.
  rewrite /quot_window.
  move: i0 => [[|l] [|h]] /=; unfold_set; simpl.
  - by split.
  - case: (Z_lt_le_dec h 0) => Hh.
    + by rewrite (quot_le_iff_neg b h c2 Hb Hh).
    + by rewrite (quot_le_iff_nonneg b h c2 Hb Hh).
  - case: (Z_lt_le_dec 0 l) => Hl.
    + by rewrite (quot_ge_iff_pos b l c2 Hb Hl).
    + by rewrite (quot_ge_iff_nonpos b l c2 Hb Hl).
  - case: (Z_lt_le_dec 0 l) => Hl; case: (Z_lt_le_dec h 0) => Hh.
    + by rewrite (quot_ge_iff_pos b l c2 Hb Hl) (quot_le_iff_neg b h c2 Hb Hh).
    + by rewrite (quot_ge_iff_pos b l c2 Hb Hl) (quot_le_iff_nonneg b h c2 Hb Hh).
    + by rewrite (quot_ge_iff_nonpos b l c2 Hb Hl) (quot_le_iff_neg b h c2 Hb Hh).
    + by rewrite (quot_ge_iff_nonpos b l c2 Hb Hl) (quot_le_iff_nonneg b h c2 Hb Hh).
Qed.

(**
    ** The two constraints, at the abstract level.

    Stated with the operands' bounds as hypotheses rather than as a γ, so that
    a [Top] bound discharges its side immediately.
 *)

(**
    Reading one bound off a membership.
 *)
Lemma itv_high_bound (i : interval) (c x : Z) :
  c ∈ γ[itv] i -> snd i = WithTop.NotTop x -> c <= x.

Proof.
  move: i => [[|l] [|h]] Hc //= [<-]; unfold_set in Hc; simpl in *; lia.
Qed.

Lemma itv_low_bound (i : interval) (c x : Z) :
  c ∈ γ[itv] i -> fst i = WithTop.NotTop x -> x <= c.

Proof.
  move: i => [[|l] [|h]] Hc //= [<-]; unfold_set in Hc; simpl in *; lia.
Qed.

Lemma quot_divisor_pos_qlow_sound (h2 l0 : WithTop.with_top Z) (c2 c1 : Z) :
  0 < c1 ->
  (forall x, h2 = WithTop.NotTop x -> c2 <= x) ->
  (forall x, l0 = WithTop.NotTop x -> x <= Z.quot c2 c1) ->
  c1 ∈ γ[itv] (quot_divisor_pos_qlow h2 l0).

Proof.
  move=> Hc1 Hh2 Hl0.
  rewrite /quot_divisor_pos_qlow.
  case: l0 Hl0 => [|z] Hl0; first by rewrite /itv_top; unfold_set.
  have Hz := Hl0 z erefl.
  rewrite /quot_bound_nz.
  case: (Z_lt_le_dec 0 z) => Hzs; case: h2 Hh2 => [|x] Hh2 //=; unfold_set; simpl; split=> //.
  - exact: (quot_divisor_upper_of_qlow c2 x z c1 Hc1 Hzs Hz (Hh2 x erefl)).
  - exact: (quot_divisor_lower_of_qlow c2 x z c1 Hc1 Hzs Hz (Hh2 x erefl)).
Qed.

Lemma quot_divisor_pos_qhigh_sound (l2 h0 : WithTop.with_top Z) (c2 c1 : Z) :
  0 < c1 ->
  (forall x, l2 = WithTop.NotTop x -> x <= c2) ->
  (forall x, h0 = WithTop.NotTop x -> Z.quot c2 c1 <= x) ->
  c1 ∈ γ[itv] (quot_divisor_pos_qhigh l2 h0).

Proof.
  move=> Hc1 Hl2 Hh0.
  rewrite /quot_divisor_pos_qhigh.
  case: h0 Hh0 => [|z] Hh0; first by rewrite /itv_top; unfold_set.
  have Hz := Hh0 z erefl.
  rewrite /quot_bound_nz.
  case: (Z_lt_le_dec z 0) => Hzs; case: l2 Hl2 => [|x] Hl2 //=; unfold_set; simpl; split=> //.
  - exact: (quot_divisor_upper_of_qhigh c2 x z c1 Hc1 Hzs Hz (Hl2 x erefl)).
  - exact: (quot_divisor_lower_of_qhigh c2 x z c1 Hc1 Hzs Hz (Hl2 x erefl)).
Qed.

(**
    ** The same two constraints, read backwards.

    A [b] the constraint admits has its window end inside the dividend
    interval — [m(b) ≤ h2] and [l2 ≤ M(b)]. Each is the matching [_sound]
    lemma run the other way, and each is one application of the [Z]
    biconditionals above to the division [quot_bound] performed: the
    adjunction that turned a quotient bound into a divisor bound turns it
    back.

    This is where truncation has to be paid for, and where the [1 ≤ b] clamp
    earns its keep. [quot_bound] truncates towards zero where the exact
    solution is a floor or a ceiling; the two differ only when the computed
    bound lands at or below [0], and there the clamp has already discarded the
    divisor. Every case below therefore uses [0 < b], and the negative-divisor
    cases go through [Z.quot_opp_r] rather than a separate rounding argument.
 *)

Lemma quot_divisor_pos_qlow_complete (h2 l0 : WithTop.with_top Z) (b : Z) :
  0 < b -> b ∈ γ[itv] (quot_divisor_pos_qlow h2 l0) ->
  non_bottom (quot_window_low l0 b, h2).

Proof.
  move=> Hb.
  rewrite /quot_divisor_pos_qlow /quot_window_low /quot_bound_nz.
  case: l0 => [|z] //=.
  case: (Z_lt_le_dec 0 z) => Hz; case: h2 => [|x] //=; unfold_set; simpl; move=> [H1 H2].
  - rewrite Primitives.quot_non_zero_quot in H2.
    have := proj1 (quot_ge_iff_pos z b x Hz Hb) H2.
    nia.
  - rewrite Primitives.quot_non_zero_quot in H1.
    have Hk : 0 < 1 - z by lia.
    have Hne : 1 - z <> 0 by lia.
    have Hopp : x ÷ (z - 1) = - (x ÷ (1 - z)).
    { have -> : z - 1 = - (1 - z) by lia.
      exact: (Z.quot_opp_r x (1 - z) Hne).
    } have Hq : 1 - b <= x ÷ (1 - z) by lia.
    have := proj1 (quot_ge_iff_nonpos (1 - z) (1 - b) x Hk (ltac:(lia) : 1 - b <= 0)) Hq.
    nia.
Qed.

Lemma quot_divisor_pos_qhigh_complete (l2 h0 : WithTop.with_top Z) (b : Z) :
  0 < b -> b ∈ γ[itv] (quot_divisor_pos_qhigh l2 h0) ->
  non_bottom (l2, quot_window_high h0 b).

Proof.
  move=> Hb.
  rewrite /quot_divisor_pos_qhigh /quot_window_high /quot_bound_nz.
  case: h0 => [|z]; first by case: l2.
  case: (Z_lt_le_dec z 0) => Hz; case: l2 => [|x] //=; unfold_set; simpl; move=> [H1 H2].
  - rewrite Primitives.quot_non_zero_quot in H2.
    have Hk : 0 < - z by lia.
    have Hne : - z <> 0 by lia.
    have Hopp : x ÷ z = - (x ÷ (- z)).
    { rewrite -(Z.quot_opp_r x (- z) Hne).
      f_equal.
      lia.
    } have Hq : x ÷ (- z) <= - b by lia.
    have := proj1 (quot_le_iff_neg (- z) (- b) x Hk (ltac:(lia) : - b < 0)) Hq.
    nia.
  - rewrite Primitives.quot_non_zero_quot in H1.
    have Hk : 0 < z + 1 by lia.
    have Hq : x ÷ (z + 1) <= b - 1 by lia.
    have := proj1 (quot_le_iff_nonneg (z + 1) (b - 1) x Hk (ltac:(lia) : 0 <= b - 1)) Hq.
    nia.
Qed.

(**
    ** The two sign halves.
 *)

Lemma interval_quot_solve_divisor_pos_sound (i2 i0 : interval) (c2 c1 : Z) :
  0 < c1 -> c2 ∈ γ[itv] i2 -> Z.quot c2 c1 ∈ γ[itv] i0 ->
  c1 ∈ γ[itv] (interval_quot_solve_divisor_pos i2 i0).

Proof.
  move=> Hc1 Hc2 Hc0.
  rewrite /interval_quot_solve_divisor_pos.
  apply/itv_strictly_positive_partE; split; last by lia.
  apply: (proj2 (itv_meet_exact _ _)); split.
  - apply: quot_divisor_pos_qlow_sound => //.
    + move=> x Hx.
      exact: (itv_high_bound i2 c2 x Hc2 Hx).
    + move=> x Hx.
      exact: (itv_low_bound i0 _ x Hc0 Hx).
  - apply: quot_divisor_pos_qhigh_sound => //.
    + move=> x Hx.
      exact: (itv_low_bound i2 c2 x Hc2 Hx).
    + move=> x Hx.
      exact: (itv_high_bound i0 _ x Hc0 Hx).
Qed.

(**
    The converse, and the witness. Every [b] the positive half returns is
    realised by an actual dividend, and finding it needs no arithmetic: the
    two [_complete] lemmas say the window overlaps [i2] at both ends, so
    [ZInterval.meet i2 (quot_window i0 b)] is non-bottom and
    [non_bottom_non_empty] hands the dividend over. The four bound comparisons
    the meet needs are exactly the two [_complete] conclusions plus the two
    operands' own non-bottomness.
 *)

Lemma itv_meet_non_bottom (a b : interval) :
  non_bottom a -> non_bottom b -> non_bottom (fst a, snd b) ->
  non_bottom (fst b, snd a) -> non_bottom (ZInterval.meet a b).

Proof.
  move: a b => [[|la] [|ha]] [[|lb] [|hb]] //=; rewrite /ZInterval.meet /=; lia.
Qed.

(**
    [l0 ≤ h0] carries over to [m(b) ≤ M(b)]: the gap the ∓1 of a zero-crossing
    quotient opens is at most [b - 1] wide, and the product already spans [b].
 *)
Lemma quot_window_non_bottom (i0 : interval) (b : Z) :
  0 < b -> non_bottom i0 -> non_bottom (quot_window i0 b).

Proof.
  move=> Hb.
  rewrite /quot_window /quot_window_low /quot_window_high.
  move: i0 => [[|l] [|h]] //= Hlh.
  case: (Z_lt_le_dec 0 l) => Hl; case: (Z_lt_le_dec h 0) => Hh; nia.
Qed.

Lemma interval_quot_solve_divisor_pos_complete (i2 i0 : interval) (c1 : Z) :
  non_bottom i2 -> non_bottom i0 ->
  c1 ∈ γ[itv] (interval_quot_solve_divisor_pos i2 i0) ->
  0 < c1 /\ exists c2, c2 ∈ γ[itv] i2 /\ Z.quot c2 c1 ∈ γ[itv] i0.

Proof.
  move=> Hnb2 Hnb0.
  move=> Hc1.
  rewrite /interval_quot_solve_divisor_pos in Hc1.
  rewrite itv_strictly_positive_part_meetE in Hc1.
  move: Hc1 => /itv_meetE [Hclamp Hc1ge].
  move: Hclamp => /itv_meetE [Hlow Hhigh].
  have Hc1 : 0 < c1 by move: Hc1ge; unfold_set; simpl; lia.
  split=> //.
  have Hnbm : non_bottom (ZInterval.meet i2 (quot_window i0 c1)).
  { apply: itv_meet_non_bottom => //.
    - exact: quot_window_non_bottom.
    - exact: (quot_divisor_pos_qhigh_complete (fst i2) (snd i0) c1 Hc1 Hhigh).
    - exact: (quot_divisor_pos_qlow_complete (snd i2) (fst i0) c1 Hc1 Hlow).
  } move: Hnbm => /non_bottom_non_empty [c2] /itv_meetE [Hc2i2 Hc2w].
  exists c2.
  split=> //.
  by apply/(quot_window_iff i0 c1 c2 Hc1).
Qed.

(**
    [interval_opp] at the level of a single member.
 *)
Lemma gamma_interval_opp (i : interval) (c : Z) :
  c ∈ γ[itv] (interval_opp i) <-> (- c) ∈ γ[itv] i.

Proof.
  move: i => [[|l] [|h]]; split; unfold_set; simpl; lia.
Qed.

(**
    ** Pushing the two negations through.

    [interval_quot_solve_divisor_neg] is [_unopt] with the [interval_opp]
    round trip pushed into the computation, and the next few lemmas are the
    steps that push it. Only the last is about division: the others say that
    [interval_opp] is an order-reversing involution, so it commutes with the
    meet and exchanges each construct with its mirror.
 *)

Lemma interval_opp_meet (a b : interval) :
  interval_opp (ZInterval.meet a b) = ZInterval.meet (interval_opp a) (interval_opp b).

Proof.
  have Hl : forall x y,
      bound_opp (ZInterval.meet_ub x y) = ZInterval.meet_lb (bound_opp x) (bound_opp y)
    by move=> [|x] [|y] //=; f_equal; lia.
  have Hu : forall x y,
      bound_opp (ZInterval.meet_lb x y) = ZInterval.meet_ub (bound_opp x) (bound_opp y)
    by move=> [|x] [|y] //=; f_equal; lia.
  by move: a b => [la ha] [lb hb] /=; rewrite Hl Hu.
Qed.

Lemma interval_opp_strictly_positive_part (i : interval) :
  interval_opp (ZInterval.itv_strictly_positive_part i) =
  ZInterval.itv_strictly_negative_part (interval_opp i).

Proof.
  have H : forall b,
      bound_opp (ZInterval.clamp_lower_bound 1 b) = ZInterval.clamp_upper_bound (-1) (bound_opp b)
    by move=> [|z] //=; f_equal; lia.
  by move: i => [l h] /=; rewrite H.
Qed.

(**
    [quot_bound_nz] with the non-zero obligation discharged, so that the
    divisor bound becomes an ordinary [Z] term and can be rewritten under. The
    proof argument is not consumed at all — [quot_non_zero x y Hy] is [Z.quot
    x y] — but it does block a plain [rewrite] on [y].
 *)
Lemma quot_bound_nz_quot (a : WithTop.with_top Z) (z : Z) (H : z <> 0) :
  quot_bound_nz a z H = match a with
                         | WithTop.Top => WithTop.Top
                         | WithTop.NotTop x => WithTop.NotTop (Z.quot x z)
                         end.

Proof.
  rewrite /quot_bound_nz; case: a => [|x] /=; first done.
  by rewrite Primitives.quot_non_zero_quot.
Qed.

(**
    The two constraints, mirrored. Each is [Z.quot_opp_r] at the one division
    it performs — no rounding argument, the two versions divide with the same
    primitive.
 *)
Lemma quot_divisor_neg_qhigh_eq (h2 h0 : WithTop.with_top Z) :
  quot_divisor_neg_qhigh h2 h0 = interval_opp (quot_divisor_pos_qlow h2 (bound_opp h0)).

Proof.
  rewrite /quot_divisor_neg_qhigh /quot_divisor_pos_qlow /itv_top /interval_opp.
  case: h0 => [|z] //=.
  case: (Z_lt_le_dec z 0) => Hz;
    case: (Z_lt_le_dec 0 (- z)) => Hz';
    try lia; rewrite !quot_bound_nz_quot; case: h2 => [|x] //=.
  - by rewrite (Z.quot_opp_r x z ltac:(lia)) Z.opp_involutive.
  - have -> : - z - 1 = - (z + 1) by lia.
    rewrite (Z.quot_opp_r x (z + 1) ltac:(lia)).
    by congr (_, _); congr WithTop.NotTop; lia.
Qed.

Lemma quot_divisor_neg_qlow_eq (l2 l0 : WithTop.with_top Z) :
  quot_divisor_neg_qlow l2 l0 = interval_opp (quot_divisor_pos_qhigh l2 (bound_opp l0)).

Proof.
  rewrite /quot_divisor_neg_qlow /quot_divisor_pos_qhigh /itv_top /interval_opp.
  case: l0 => [|z] //=.
  case: (Z_lt_le_dec 0 z) => Hz;
    case: (Z_lt_le_dec (- z) 0) => Hz';
    try lia; rewrite !quot_bound_nz_quot; case: l2 => [|x] //=.
  - by rewrite (Z.quot_opp_r x z ltac:(lia)) Z.opp_involutive.
  - have -> : - z + 1 = - (z - 1) by lia.
    rewrite (Z.quot_opp_r x (z - 1) ltac:(lia)).
    by congr (_, _); congr WithTop.NotTop; lia.
Qed.

(**
    The optimized negative half is the specification. Everything below is
    proved on [_unopt], through [gamma_interval_opp]; this is what carries it
    to the function that gets extracted.
 *)
Lemma interval_quot_solve_divisor_neg_eq (i2 i0 : interval) :
  interval_quot_solve_divisor_neg i2 i0 = interval_quot_solve_divisor_neg_unopt i2 i0.

Proof.
  move: i0 => [l0 h0].
  rewrite /interval_quot_solve_divisor_neg /interval_quot_solve_divisor_neg_unopt
    /interval_quot_solve_divisor_pos /= quot_divisor_neg_qhigh_eq quot_divisor_neg_qlow_eq
    -interval_opp_meet -interval_opp_strictly_positive_part.
  done.
Qed.

Lemma interval_quot_solve_divisor_neg_sound (i2 i0 : interval) (c2 c1 : Z) :
  c1 < 0 -> c2 ∈ γ[itv] i2 -> Z.quot c2 c1 ∈ γ[itv] i0 ->
  c1 ∈ γ[itv] (interval_quot_solve_divisor_neg i2 i0).

Proof.
  move=> Hc1 Hc2 Hc0.
  rewrite interval_quot_solve_divisor_neg_eq /interval_quot_solve_divisor_neg_unopt.
  apply/gamma_interval_opp.
  apply: (interval_quot_solve_divisor_pos_sound i2 (interval_opp i0) c2 (- c1));
    [lia | exact: Hc2 |].
  apply/gamma_interval_opp.
  have Hne : c1 <> 0 by lia.
  rewrite (Z.quot_opp_r c2 c1 Hne) Z.opp_involutive.
  exact: Hc0.
Qed.

(**
    The negative half's converse, the same way round: [gamma_interval_opp] is
    already a biconditional, so this is [..._neg_sound] read backwards.
 *)
Lemma interval_quot_solve_divisor_neg_complete (i2 i0 : interval) (c1 : Z) :
  non_bottom i2 -> non_bottom i0 ->
  c1 ∈ γ[itv] (interval_quot_solve_divisor_neg i2 i0) ->
  c1 < 0 /\ exists c2, c2 ∈ γ[itv] i2 /\ Z.quot c2 c1 ∈ γ[itv] i0.

Proof.
  move=> Hnb2 Hnb0.
  rewrite interval_quot_solve_divisor_neg_eq /interval_quot_solve_divisor_neg_unopt.
  move=> /gamma_interval_opp Hin.
  have Hnb0' := interval_opp_preserves_non_bottom _ Hnb0.
  have [Hpos [c2 [Hc2 Hq]]] :=
    interval_quot_solve_divisor_pos_complete i2 (interval_opp i0) (- c1) Hnb2 Hnb0' Hin.
  split; first lia.
  exists c2.
  split=> //.
  move: Hq => /gamma_interval_opp Hq.
  have -> : Z.quot c2 c1 = - (Z.quot c2 (- c1)).
  { rewrite -(Z.quot_opp_r c2 (- c1) (ltac:(lia) : - c1 <> 0)).
    f_equal.
    lia.
  } exact: Hq.
Qed.

(**
    ** The join of the two halves.

    [join_possibly_bottom] ([ZInterval.v]) is [CollapsedBottom]'s
    [join_lub_compat] ([AbstractionCombination.v]) at the interval domain,
    written on [non_bottomb] so that it stays in the computational core: a
    γ-empty half is dropped rather than contributing its stray bounds.
 *)

(**
    Both are [join_sound] ([AbstractLattice.v]) at the computational join,
    which [itv_join_eq_al_join] identifies with the lattice's ⊔. Proved that
    way rather than by cases on the bounds, so that they follow the lattice
    rather than [ZInterval.join]'s definition.
 *)
Lemma itv_join_sound_l (a b : interval) (c : Z) :
  c ∈ γ[itv] a -> c ∈ γ[itv] (ZInterval.join a b).

Proof.
  rewrite itv_join_eq_al_join => Hc; by apply: join_sound; unfold_set; left.
Qed.

Lemma itv_join_sound_r (a b : interval) (c : Z) :
  c ∈ γ[itv] b -> c ∈ γ[itv] (ZInterval.join a b).

Proof.
  rewrite itv_join_eq_al_join => Hc; by apply: join_sound; unfold_set; right.
Qed.

Lemma join_possibly_bottom_sound_l (a b : interval) (c : Z) :
  c ∈ γ[itv] a -> c ∈ γ[itv] (join_possibly_bottom a b).

Proof.
  move=> Hc.
  rewrite /join_possibly_bottom.
  have Hnb : ZInterval.non_bottomb a by apply/non_bottombP; apply/non_bottom_non_empty; exists c.
  rewrite Hnb.
  case: (ZInterval.non_bottomb b) => //.
  exact: itv_join_sound_l.
Qed.

Lemma join_possibly_bottom_sound_r (a b : interval) (c : Z) :
  c ∈ γ[itv] b -> c ∈ γ[itv] (join_possibly_bottom a b).

Proof.
  move=> Hc.
  rewrite /join_possibly_bottom.
  have Hnb : ZInterval.non_bottomb b by apply/non_bottombP; apply/non_bottom_non_empty; exists c.
  rewrite Hnb.
  case: (ZInterval.non_bottomb a) => //.
  exact: itv_join_sound_r.
Qed.

Lemma join_possibly_bottom_lower_bound (a b x : interval) :
  a ⊑[itv] x -> b ⊑[itv] x -> join_possibly_bottom a b ⊑[itv] x.

Proof.
  move=> Ha Hb.
  rewrite /join_possibly_bottom.
  case: (ZInterval.non_bottomb a) => //.
  case: (ZInterval.non_bottomb b) => //.
  exact: join_lub.
Qed.

(**
    The precision counterpart of the three lemmas above:
    [join_possibly_bottom] is the *best* abstraction of the union, given that
    each side is an exact representation of its own part. Where both sides are
    inhabited this is [is_alpha_join_split]; where one is γ-empty its part is
    empty too, the union collapses, and the surviving side is exact on the
    nose.

    [MostPrecise] rather than [BestAbstraction] because the empty case has to
    be covered: [itv] has no ⊑-least element, but [UpperBoundInPrecision] is
    stated at γ, where ∅ ⊆ γ a holds of every [a].
 *)

(**
    Each side goes into [itv_canon_ad] by [is_alpha_itv_canon_iff], and the
    two are joined by [is_alpha_join_split] — no case analysis anywhere,
    because the γ-empty side is ⊑-least on the collapsed domain instead of
    needing to be argued away. That also makes the conclusion strictly
    stronger than the [MostPrecise] below, which is all raw [itv] can express.

    [itv_canon_join_eq] ([ZIntervalTheory.v]) is what licenses reading
    [join_possibly_bottom] as [itv_canon_ajsl]'s ⊔, where the join is a
    genuine LUB — which [ZInterval.join] is not. Everything here rests on
    that.
 *)
Lemma join_possibly_bottom_is_alpha_canon (a b : interval) (S Sa Sb : ℘ Z) :
  S ⊆⊇ Sa ∪ Sb -> γ[itv] a ⊆⊇ Sa -> γ[itv] b ⊆⊇ Sb ->
  IsAlpha (A:=itv_canon_ad) (join_possibly_bottom a b) S.

Proof.
  move=> HS Ha Hb.
  (* Exactness gives soundness outright; and when the side is non-bottom it
     is the best abstraction of its own γ, hence of its part.
   *)
  have Hside : forall (i : interval) (T : ℘ Z), γ[itv] i ⊆⊇ T -> IsAlpha (A:=itv_canon_ad) i T.
  { move=> i T Hi.
    apply/is_alpha_itv_canon_iff.
    split; first exact: (proj2 Hi).
    move=> Ei.
    have Hnb : non_bottom i by apply/non_bottombP; rewrite Ei.
    exact: (is_alpha_set_equiv _ _ _ Hi (non_bottom_is_alpha_gamma _ Hnb)).
  } rewrite -itv_canon_join_eq.
  exact: (is_alpha_join_split itv_canon_ajsl _ _ _ _ _ HS (Hside _ _ Ha) (Hside _ _ Hb)).
Qed.

Lemma join_possibly_bottom_most_precise (a b : interval) (S Sa Sb : ℘ Z) :
  S ⊆⊇ Sa ∪ Sb -> γ[itv] a ⊆⊇ Sa -> γ[itv] b ⊆⊇ Sb ->
  MostPrecise (A:=itv) (join_possibly_bottom a b) S.

Proof.
  move=> HS Ha Hb.
  (* [MostPrecise] reads the abstraction only through γ, and [itv_canon_ad]
     has the same γ as [itv]; so the collapsed-domain α transfers verbatim.
   *)
  exact: (is_alpha_is_most_precise (A:=itv_canon_ad) _ _
    (join_possibly_bottom_is_alpha_canon a b S Sa Sb HS Ha Hb)).
Qed.

(**
    ** The transfer function.
 *)

(**
    Each solve half is clamped off zero by its own trailing sign clamp, so its
    inner bound is finite and on the right side of [0]. Two things rest on
    that: the ∓1 clamp the split puts on the incoming divisor is redundant,
    and a sign-definite divisor kills one of the halves outright.
 *)
Lemma interval_quot_solve_divisor_pos_low (i2 i0 : interval) :
  exists v h, 1 <= v /\ interval_quot_solve_divisor_pos i2 i0 = (WithTop.NotTop v, h).

Proof.
  rewrite /interval_quot_solve_divisor_pos /ZInterval.itv_strictly_positive_part.
  case: (ZInterval.meet _ _) => [[|z] h] /=.
  - by exists 1, h.
  - by exists (Z.max z 1), h; split=> //; lia.
Qed.

Lemma interval_quot_solve_divisor_neg_high (i2 i0 : interval) :
  exists l v, v <= -1 /\ interval_quot_solve_divisor_neg i2 i0 = (l, WithTop.NotTop v).

Proof.
  rewrite /interval_quot_solve_divisor_neg /ZInterval.itv_strictly_negative_part.
  case: (ZInterval.meet _ _) => [l [|z]] /=.
  - by exists l, (-1).
  - by exists l, (Z.min z (-1)); split=> //; lia.
Qed.

(**
    A sign-definite divisor rules out one of the two halves, and it does so
    through the *clamp* the half carries rather than through anything about
    division: a divisor with [l1 >= 0] cannot meet an interval capped at [-1].
    This is what the [classify] dispatch of
    [interval_quot_solve_divisor_split] exploits, and what makes it agree with
    the undispatched [_unopt].
 *)
Lemma itv_meet_bottom_of_classify_Pos (i1 x : interval) (v : Z) :
  classify i1 = Pos -> snd x = WithTop.NotTop v -> v <= -1 ->
  ZInterval.non_bottomb (ZInterval.meet i1 x) = false.

Proof.
  move: i1 x => [l1 h1] [lx hx] /classify_Pos_inv [z [-> Hz]] /= -> Hv.
  by move: h1 lx => [|hz] [|w] /=; apply/Z.leb_gt; lia.
Qed.

Lemma itv_meet_bottom_of_classify_Neg (i1 x : interval) (v : Z) :
  classify i1 = Neg -> fst x = WithTop.NotTop v -> 1 <= v ->
  ZInterval.non_bottomb (ZInterval.meet i1 x) = false.

Proof.
  move: i1 x => [l1 h1] [lx hx] /classify_Neg_inv [z [-> Hz]] /= -> Hv.
  by move: l1 hx => [|w] [|hz] /=; apply/Z.leb_gt; lia.
Qed.

(**
    A gamma-empty interval has no members, in the boolean form the split uses.
 *)
Lemma itv_non_bottomb_false_empty (i : interval) (c : Z) :
  ZInterval.non_bottomb i = false -> c ∈ γ[itv] i -> False.

Proof.
  move=> Hi Hc.
  have Hnb : non_bottom i by apply/non_bottom_non_empty; exists c.
  by move: (introT (non_bottombP i) Hnb); rewrite Hi.
Qed.

(**
    The optimized split against the specification. The two clamps on [i1] come
    off by absorption, on the nose; the [classify] dispatch does not, and this
    is the one place where the two versions differ as terms. When a sign half
    is ruled out, [join_possibly_bottom] returns the other one — structurally,
    so the dispatch is an equality — *except* when both halves are
    gamma-empty, where the left bias returns the positive half's bounds and
    the [Neg] branch returns the negative half's. Both are bottom, and gamma
    is all that [Overapproximates] and [MostPrecise] read.
 *)
Lemma interval_quot_solve_divisor_split_gamma_eq (i2 i1 i0 : interval) :
  γ[itv] (interval_quot_solve_divisor_split_unopt i2 i1 i0)
  ⊆⊇ γ[itv] (interval_quot_solve_divisor_split i2 i1 i0).

Proof.
  have [ln [vn [Hvn Hn]]] := interval_quot_solve_divisor_neg_high i2 i0.
  have [vp [hp [Hvp Hp]]] := interval_quot_solve_divisor_pos_low i2 i0.
  rewrite /interval_quot_solve_divisor_split_unopt /interval_quot_solve_divisor_split Hn Hp
    (itv_meet_strictly_negative_part_absorb i1 (ln, WithTop.NotTop vn) vn erefl Hvn)
    (itv_meet_strictly_positive_part_absorb i1 (WithTop.NotTop vp, hp) vp erefl Hvp)
    /ZInterval.join_possibly_bottom.
  case Hc: (classify i1).
  - rewrite (itv_meet_bottom_of_classify_Pos i1 (ln, WithTop.NotTop vn) vn Hc erefl Hvn).
    by split.
  - rewrite (itv_meet_bottom_of_classify_Neg i1 (WithTop.NotTop vp, hp) vp Hc erefl Hvp).
    case HA: (ZInterval.non_bottomb (ZInterval.meet i1 (ln, WithTop.NotTop vn))); first by split.
    (* Both halves are gamma-empty: the divisor is contradicted outright, and
       the two versions disagree on which empty pair to report.
     *)
    split=> c Hc'; exfalso.
    + exact: (itv_non_bottomb_false_empty _ c
        (itv_meet_bottom_of_classify_Neg i1 (WithTop.NotTop vp, hp) vp Hc erefl Hvp) Hc').
    + exact: (itv_non_bottomb_false_empty _ c HA Hc').
  - by split.
Qed.

(**
    [Overapproximates] and [MostPrecise] are stated only through gamma, so a
    gamma-equivalence carries them across. Generic, but kept here with their
    only client rather than added to [Abstraction.v] unused — the rule of
    [todo/quot_backward_divisor.md] §6.
 *)
Lemma overapproximates_gamma_equiv `{A : abstraction C} (a b : A) (S : propset C) :
  γ[A] a ⊆⊇ γ[A] b -> Overapproximates a S -> Overapproximates b S.

Proof.
  by move=> [Hab _] Hover c /Hover /Hab.
Qed.

Lemma most_precise_gamma_equiv `{A : abstraction C} (a b : A) (S : propset C) :
  γ[A] a ⊆⊇ γ[A] b -> MostPrecise a S -> MostPrecise b S.

Proof.
  move=> [Hab Hba] [Hover Hopt].
  split.
  - exact: (overapproximates_gamma_equiv a b S (conj Hab Hba) Hover).
  - move=> x Hx c Hc.
    exact: (Hopt x Hx c (Hba c Hc)).
Qed.

Lemma backward_interval_quot_divisor_lower_bound (i2 i1 i0 : nb_interval) :
  backward_interval_quot_divisor i2 i1 i0 ⊑[itv] (`i1).

Proof.
  rewrite /backward_interval_quot_divisor /interval_quot_solve_divisor_split.
  case: (classify (`i1)); [exact: itv_meet_lower_bound_l ..|].
  by apply: join_possibly_bottom_lower_bound; exact: itv_meet_lower_bound_l.
Qed.

Lemma backward_interval_quot_divisor_sound :
  ternary_overapproximation nbitv nbitv nbitv itv backward_interval_quot_divisor
    collecting_quot_backward_right.

Proof.
  move=> [i2 H2] [i1 H1] [i0 H0].
  move=> c1 Hc1.
  unfold_set in Hc1.
  move: Hc1 => [c2 [c0 [Hc2 [Hc1 [Hc0 [Hne Heq]]]]]].
  rewrite /backward_interval_quot_divisor /=.
  apply: (proj1 (interval_quot_solve_divisor_split_gamma_eq _ _ _)).
  rewrite /interval_quot_solve_divisor_split_unopt.
  have Hq : Z.quot c2 c1 ∈ γ[itv] i0 by rewrite Heq; exact: Hc0.
  have Hnz : c1 <> 0 by move: Hne; rewrite /is_nonzero.
  case: (Z.le_gt_cases 0 c1) => Hs.
  - (* a positive divisor: the positive half, which carries the [1 ≤ c1]
       clamp *)
    apply: join_possibly_bottom_sound_r.
    rewrite itv_strictly_positive_part_meetE.
    apply: (proj2 (itv_meet_exact _ _)); split.
    + apply: (proj2 (itv_meet_exact _ _)); split; first exact: Hc1.
      unfold_set; simpl; lia.
    + apply: (interval_quot_solve_divisor_pos_sound i2 i0 c2 c1); [lia | exact: Hc2 | exact: Hq].
  - apply: join_possibly_bottom_sound_l.
    rewrite itv_strictly_negative_part_meetE.
    apply: (proj2 (itv_meet_exact _ _)); split.
    + apply: (proj2 (itv_meet_exact _ _)); split; first exact: Hc1.
      unfold_set; simpl; lia.
    + apply: (interval_quot_solve_divisor_neg_sound i2 i0 c2 c1); [lia | exact: Hc2 | exact: Hq].
Qed.


(**
    ** Bestness.

    Each sign half is not merely sound but *exactly* its part of the backward
    set: the solve set is convex there and the meet with [i1] is taken inside,
    so nothing is added and nothing is lost. The two halves partition the
    backward set, since [is_nonzero] rules the split point out, and
    [join_possibly_bottom_most_precise] does the rest.

    [_best], not [_alpha_complete]: all three operands stay at γ, and that is
    a boundary rather than a missing proof — see
    [backward_quot_divisor_not_alpha_complete] at the end of this file.
 *)

(**
    Two views, in the style of [itv_meetE] ([ZIntervalTheory.v]): the sign
    halves and the backward set, each taken apart once here instead of at
    every use. [itv_strictly_positive_partE] / [itv_strictly_negative_partE]
    (in [ZIntervalTheory.v]) are the carrier-level views without a [classify]
    hypothesis, which is not available here.
 *)

(**
    Stated on arbitrary sets rather than on concretizations: nothing here
    needs the operands to be γ's, and the sign split below uses it too.
 *)
Lemma backward_divisor_memE (S2 S1 S0 : ℘ Z) (c1 : Z) :
  c1 ∈ collecting_quot_backward_right S2 S1 S0 <->
  c1 <> 0 /\ c1 ∈ S1 /\ exists c2, c2 ∈ S2 /\ Z.quot c2 c1 ∈ S0.

Proof.
  split.
  - move=> H.
    unfold_set in H.
    move: H => [c2 [c0 [Hc2 [Hi1 [Hc0 [Hne Heq]]]]]].
    rewrite /is_nonzero in Hne.
    by split=> //; split=> //; exists c2; split=> //; rewrite Heq.
  - move=> [Hne [Hi1 [c2 [Hc2 Hq]]]].
    unfold_set.
    by exists c2, (Z.quot c2 c1); do 4 (split=> //).
Qed.

Lemma interval_quot_solve_divisor_pos_half_exact (i2 i1 i0 : interval) :
  non_bottom i2 -> non_bottom i0 ->
  γ[itv] (ZInterval.meet (ZInterval.itv_strictly_positive_part i1)
    (interval_quot_solve_divisor_pos i2 i0)) ⊆⊇
  (collecting_quot_backward_right (γ[itv] i2) (γ[itv] i1) (γ[itv] i0))
    ∩ {[ c1 : Z | 0 < c1 ]}.

Proof.
  move=> Hnb2 Hnb0.
  split=> c1.
  - move=> /itv_meetE [/itv_strictly_positive_partE [Hi1 _] Hsolve].
    have [Hpos [c2 [Hc2 Hq]]] := interval_quot_solve_divisor_pos_complete i2 i0 c1 Hnb2 Hnb0 Hsolve.
    unfold_set.
    split; last exact: Hpos.
    by apply/backward_divisor_memE; split; [lia | split=> //; exists c2].
  - move=> Hc1.
    unfold_set in Hc1.
    move: Hc1 => [Hbw Hsign].
    simpl in Hsign.
    move: Hbw => /backward_divisor_memE [_ [Hi1 [c2 [Hc2 Hq]]]].
    apply/itv_meetE; split.
    + by apply/itv_strictly_positive_partE; split=> //; lia.
    + exact: (interval_quot_solve_divisor_pos_sound i2 i0 c2 c1 Hsign Hc2 Hq).
Qed.

Lemma interval_quot_solve_divisor_neg_half_exact (i2 i1 i0 : interval) :
  non_bottom i2 -> non_bottom i0 ->
  γ[itv] (ZInterval.meet (ZInterval.itv_strictly_negative_part i1)
    (interval_quot_solve_divisor_neg i2 i0)) ⊆⊇
  (collecting_quot_backward_right (γ[itv] i2) (γ[itv] i1) (γ[itv] i0))
    ∩ {[ c1 : Z | c1 < 0 ]}.

Proof.
  move=> Hnb2 Hnb0.
  split=> c1.
  - move=> /itv_meetE [/itv_strictly_negative_partE [Hi1 _] Hsolve].
    have [Hneg [c2 [Hc2 Hq]]] := interval_quot_solve_divisor_neg_complete i2 i0 c1 Hnb2 Hnb0 Hsolve.
    unfold_set.
    split; last exact: Hneg.
    by apply/backward_divisor_memE; split; [lia | split=> //; exists c2].
  - move=> Hc1.
    unfold_set in Hc1.
    move: Hc1 => [Hbw Hsign].
    simpl in Hsign.
    move: Hbw => /backward_divisor_memE [_ [Hi1 [c2 [Hc2 Hq]]]].
    apply/itv_meetE; split.
    + by apply/itv_strictly_negative_partE; split=> //; lia.
    + exact: (interval_quot_solve_divisor_neg_sound i2 i0 c2 c1 Hsign Hc2 Hq).
Qed.

(**
    A set of non-zero integers is the union of its two sign parts: there is
    nothing on the seam. Nothing about intervals or division enters — the
    backward set qualifies only because the guard [is_nonzero] puts it in
    ([backward_divisor_memE]), and that is exactly why the two halves below
    partition it.
 *)
Lemma propset_sign_split (S : ℘ Z) :
  (forall c, c ∈ S -> c <> 0) ->
  S ⊆⊇ (S ∩ {[ c : Z | c < 0 ]}) ∪ (S ∩ {[ c : Z | 0 < c ]}).

Proof.
  move=> Hnz; split=> c Hc.
  - have Hne := Hnz c Hc; unfold_set.
    case: (Z.lt_ge_cases c 0) => Hs; [left | right]; split=> //; lia.
  - unfold_set in Hc.
    by case: Hc => [[? _]|[? _]].
Qed.

(**
    The meet with the incoming divisor is taken inside each sign half, where
    the solve set is convex, so each half is exactly its part of the backward
    set ([interval_quot_solve_divisor_{pos,neg}_half_exact], above) and
    nothing is lost to the join. The convexity is [quot_window_iff]: at a
    fixed divisor the dividends that land in [γ i0] form an interval, so the
    two [_complete] lemmas can hand back a witness rather than a bound.
    Bestness at γ is the ceiling here — α-completeness fails on every quadrant
    ([backward_quot_divisor_not_alpha_complete]) — and it matches the
    measurement (0 loose on all 3 581 577 boxes over [[-8,8]],
    [todo/quot_backward_divisor.md]).

    The empty case is why this is [ternary_best] ([MostPrecise]) rather than a
    [BestAbstraction]: the function reports a contradiction by returning a
    γ-empty interval, no interval is α of ∅, but [UpperBoundInPrecision] is
    stated at γ and ∅ ⊆ γ a always.
 *)
Theorem backward_interval_quot_divisor_best :
  ternary_best nbitv nbitv nbitv itv backward_interval_quot_divisor
    collecting_quot_backward_right.

Proof.
  move=> [i2 H2] [i1 H1] [i0 H0].
  rewrite /backward_interval_quot_divisor /=.
  apply: (most_precise_gamma_equiv _ _ _ (interval_quot_solve_divisor_split_gamma_eq i2 i1 i0)).
  rewrite /interval_quot_solve_divisor_split_unopt.
  (* The guard is what makes the two sign halves a partition.
   *)
  have Hnz : forall c,
      c ∈ collecting_quot_backward_right (γ[itv] i2) (γ[itv] i1) (γ[itv] i0) -> c <> 0
    by move=> c /backward_divisor_memE [].
  apply: (join_possibly_bottom_most_precise _ _ _ _ _ (propset_sign_split _ Hnz)).
  - exact: interval_quot_solve_divisor_neg_half_exact.
  - exact: interval_quot_solve_divisor_pos_half_exact.
Qed.

(**
    * The low-level refinement interface.

    Both refinements are meets — the divisor's is a meet inside each sign half
    — so both sides of the [option] protocol are discharged by a "only ever
    shrinks" lemma.
 *)

(**
    * Refining the dividend, after the divisor.

    The dividend's transfer function is *not* [refine_by i2] of the solve step
    above — the solve set is non-convex (a union of blocks [W(c1)]), and
    meeting its hull with [i2] re-admits gaps from blocks that miss [γ i2].
    The repair is to refine the divisor first, which drops exactly those
    blocks, then solve the dividend against the refined divisor per sign half,
    then meet with [i2]. Bestness rests on three lemmas: the solve step is
    best ([interval_quot_solve_dividend_split_best]), the divisor's refinement
    is best so every surviving block meets [γ i2]
    ([backward_interval_quot_divisor_best]), and the covering lemma
    [itv_meet_is_alpha_covered] commutes hull with intersection under that
    condition. The covering lemma is generic, in [ZIntervalTheory.v], and
    mentions no division; see [todo/quot_backward_dividend.md] §5.

    [impl_backward_interval_quot] computes each sign half once and shares it
    between the two refinements, so this dependence on the divisor's
    refinement costs no extra divisions. See [ZIntervalBackwardOps.v] and the
    header.

    [backward_interval_quot_dividend] solves the dividend against the
    *refined* divisor, one sign half at a time. Soundness needs nothing new: a
    witnessing divisor lands in its own half by the divisor side's soundness,
    the half is therefore inhabited so the guard passes, and the solve step
    does the rest.
 *)

Lemma interval_quot_dividend_from_divisor_half_sound (i2 F i0 : interval)
    (c2 c1 : Z) :
  c1 <> 0 -> c2 ∈ γ[itv] i2 -> c1 ∈ γ[itv] F -> Z.quot c2 c1 ∈ γ[itv] i0 ->
  c2 ∈ γ[itv] (interval_quot_dividend_from_divisor_half i2 F i0).

Proof.
  move=> Hnz Hc2 HF Hq.
  rewrite /interval_quot_dividend_from_divisor_half.
  have Hnb : ZInterval.non_bottomb F
    by apply/non_bottombP; apply/non_bottom_non_empty; exists c1.
  rewrite Hnb.
  apply/itv_meetE; split=> //.
  apply: interval_quot_solve_dividend_sound.
  unfold_set.
  by exists c1, (Z.quot c2 c1); do 3 (split=> //).
Qed.

(**
    Each half, at the sign its solve half is about. Both are
    [interval_quot_dividend_from_divisor_half_sound] with the divisor placed
    in its half by the divisor side's own soundness.
 *)
Lemma interval_quot_dividend_from_divisor_half_sound_pos (i2 i1 i0 : interval)
    (c2 c1 : Z) :
  0 < c1 -> c2 ∈ γ[itv] i2 -> c1 ∈ γ[itv] i1 -> Z.quot c2 c1 ∈ γ[itv] i0 ->
  c2 ∈ γ[itv] (interval_quot_dividend_from_divisor_half i2
    (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0)) i0).

Proof.
  move=> Hs Hc2 Hc1 Hq.
  apply: (interval_quot_dividend_from_divisor_half_sound i2 _ i0 c2 c1) => //; first lia.
  apply/itv_meetE; split=> //.
  exact: (interval_quot_solve_divisor_pos_sound i2 i0 c2 c1 Hs Hc2 Hq).
Qed.

Lemma interval_quot_dividend_from_divisor_half_sound_neg (i2 i1 i0 : interval)
    (c2 c1 : Z) :
  c1 < 0 -> c2 ∈ γ[itv] i2 -> c1 ∈ γ[itv] i1 -> Z.quot c2 c1 ∈ γ[itv] i0 ->
  c2 ∈ γ[itv] (interval_quot_dividend_from_divisor_half i2
    (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0)) i0).

Proof.
  move=> Hs Hc2 Hc1 Hq.
  apply: (interval_quot_dividend_from_divisor_half_sound i2 _ i0 c2 c1) => //; first lia.
  apply/itv_meetE; split=> //.
  exact: (interval_quot_solve_divisor_neg_sound i2 i0 c2 c1 Hs Hc2 Hq).
Qed.

(**
    On a sign-definite divisor the dispatch picks the only half a legal
    divisor can be in — [classify_{Pos,Neg}_inv] is what turns the
    classification into that sign fact.
 *)
Lemma interval_quot_dividend_refine_sound (i2 i1 i0 : interval) (c2 c1 : Z) :
  c1 <> 0 -> c2 ∈ γ[itv] i2 -> c1 ∈ γ[itv] i1 -> Z.quot c2 c1 ∈ γ[itv] i0 ->
  c2 ∈ γ[itv] (interval_quot_dividend_refine i2 i1 i0).

Proof.
  move=> Hnz Hc2 Hc1 Hq.
  rewrite /interval_quot_dividend_refine.
  move: i1 Hc1 => [l1 h1] Hc1.
  case E: (classify (l1, h1)).
  - have [z [Hz1 Hz2]] := classify_Pos_inv _ _ E.
    have Hlow : z <= c1 by apply: (itv_low_bound (l1, h1) c1 z Hc1); rewrite /= Hz1.
    exact: (interval_quot_dividend_from_divisor_half_sound_pos i2 (l1, h1) i0 c2 c1
      (ltac:(lia)) Hc2 Hc1 Hq).
  - have [z [Hz1 Hz2]] := classify_Neg_inv _ _ E.
    have Hhigh : c1 <= z by apply: (itv_high_bound (l1, h1) c1 z Hc1); rewrite /= Hz1.
    exact: (interval_quot_dividend_from_divisor_half_sound_neg i2 (l1, h1) i0 c2 c1
      (ltac:(lia)) Hc2 Hc1 Hq).
  - case: (Z.le_gt_cases 0 c1) => Hs.
    + apply: join_possibly_bottom_sound_r.
      exact: (interval_quot_dividend_from_divisor_half_sound_pos i2 (l1, h1) i0 c2 c1
        (ltac:(lia)) Hc2 Hc1 Hq).
    + apply: join_possibly_bottom_sound_l.
      exact: (interval_quot_dividend_from_divisor_half_sound_neg i2 (l1, h1) i0 c2 c1
        (ltac:(lia)) Hc2 Hc1 Hq).
Qed.

Lemma backward_interval_quot_dividend_sound :
  ternary_overapproximation nbitv nbitv nbitv itv backward_interval_quot_dividend
    collecting_quot_backward_left.

Proof.
  move=> [i2 H2] [i1 H1] [i0 H0] c2 Hc2.
  unfold_set in Hc2.
  move: Hc2 => [c1 [c0 [Hi2 [Hc1 [Hc0 [Hne Heq]]]]]].
  have Hnz : c1 <> 0 by move: Hne; rewrite /is_nonzero.
  have Hq : Z.quot c2 c1 ∈ γ[itv] i0 by rewrite Heq; exact: Hc0.
  exact: (interval_quot_dividend_refine_sound i2 i1 i0 c2 c1 Hnz Hi2 Hc1 Hq).
Qed.

(**
    ** Bestness of the dividend, one sign half at a time.

    The half is [meet i2] of the solve set taken over the *feasible* divisors,
    and a feasible divisor is precisely one whose block meets [γ i2] — which
    is the covering lemma's hypothesis, handed over by the divisor side's
    [_half_exact]. The blocks themselves are [quot_window], intervals by
    [quot_window_iff].
 *)

(**
    [interval_quot_dividend_from_divisor_half] solves with the unsplit
    [interval_quot_solve_dividend] because its [F] is always a solved half,
    already clamped off zero; the two bestness proofs below need the split
    form, which these two lemmas hand back. On a divisor whose low bound is [≥
    1] the [classify] inside [_split] is [Pos] and
    [itv_strictly_positive_part] is the identity, so the two agree;
    symmetrically on a high bound [≤ -1]. The positive side needs no
    [non_bottom]: [classify_pos_of_low] does not.
 *)
Lemma interval_quot_solve_dividend_split_pos_preclamped (F i0 : interval) (l0 : Z) :
  fst F = WithTop.NotTop l0 -> 1 <= l0 ->
  interval_quot_solve_dividend_split F i0 = interval_quot_solve_dividend F i0.

Proof.
  move=> Hfst Hlo.
  have Hpos : 0 < l0 by lia.
  case: F Hfst => [a b] Hfst.
  simpl in Hfst.
  subst a.
  rewrite /interval_quot_solve_dividend_split (classify_pos_of_low l0 b Hpos)
    /ZInterval.itv_strictly_positive_part /ZInterval.clamp_lower_bound /=.
  by do 3 f_equal; lia.
Qed.

Lemma interval_quot_solve_dividend_split_neg_preclamped (F i0 : interval) (h0 : Z) :
  snd F = WithTop.NotTop h0 -> h0 <= -1 -> non_bottom F ->
  interval_quot_solve_dividend_split F i0 = interval_quot_solve_dividend F i0.

Proof.
  move=> Hsnd Hhi Hnb.
  have Hneg : h0 < 0 by lia.
  case: F Hsnd Hnb => [a b] Hsnd Hnb.
  simpl in Hsnd.
  subst b.
  rewrite /interval_quot_solve_dividend_split (classify_neg_of_high a h0 Hneg Hnb)
    /ZInterval.itv_strictly_negative_part /ZInterval.clamp_upper_bound /=.
  by do 3 f_equal; lia.
Qed.

(**
    [F] is the feasible positive divisors on the nose: the clamp the divisor's
    [_half_exact] carries is absorbed by the meet
    ([itv_meet_strictly_positive_part_absorb]).
 *)
Lemma quot_dividend_F_pos_exact (i2 i1 i0 : interval) :
  non_bottom i2 -> non_bottom i0 ->
  γ[itv] (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0)) ⊆⊇
  (collecting_quot_backward_right (γ[itv] i2) (γ[itv] i1) (γ[itv] i0)) ∩ {[ c1 : Z | 0 < c1 ]}.

Proof.
  move=> Hnb2 Hnb0.
  have [vp [hp [Hvp Hp]]] := interval_quot_solve_divisor_pos_low i2 i0.
  have Hfst : fst (interval_quot_solve_divisor_pos i2 i0) = WithTop.NotTop vp by rewrite Hp.
  rewrite -(itv_meet_strictly_positive_part_absorb i1 _ vp Hfst Hvp).
  exact: interval_quot_solve_divisor_pos_half_exact.
Qed.

Lemma interval_quot_dividend_from_divisor_half_pos_is_alpha (i2 i1 i0 : interval) :
  non_bottom i2 -> non_bottom i0 ->
  (exists c2, c2 ∈ γ[itv] i2 /\ exists c1,
     0 < c1 /\ c1 ∈ γ[itv] i1 /\ Z.quot c2 c1 ∈ γ[itv] i0) ->
  IsAlpha (A:=itv)
    (interval_quot_dividend_from_divisor_half i2
       (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0)) i0)
    {[ c2 | c2 ∈ γ[itv] i2 /\ exists c1,
        0 < c1 /\ c1 ∈ γ[itv] i1 /\ Z.quot c2 c1 ∈ γ[itv] i0 ]}.

Proof.
  move=> Hnb2 Hnb0 Hex.
  have HF := quot_dividend_F_pos_exact i2 i1 i0 Hnb2 Hnb0.
  set F := ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0).
  (* a member of γF is a feasible positive divisor, and conversely *)
  have HFmem : forall c1,
      c1 ∈ γ[itv] F <->
      (0 < c1 /\ c1 ∈ γ[itv] i1 /\ exists c2, c2 ∈ γ[itv] i2 /\ Z.quot c2 c1 ∈ γ[itv] i0).
  { move=> c1; split.
    - move=> /(proj1 HF) Hc.
      unfold_set in Hc.
      move: Hc => [Hbw Hsign].
      move: Hbw => /backward_divisor_memE [_ [Hi1 [c2 [Hc2 Hq]]]].
      by split; [exact: Hsign | split=> //; exists c2].
    - move=> [Hs [Hi1 [c2 [Hc2 Hq]]]].
      apply: (proj2 HF).
      unfold_set.
      split=> //.
      by apply/backward_divisor_memE; split; [lia | split=> //; exists c2].
  } have HexF : exists c, c ∈ γ[itv] F /\ c <> 0.
  { move: Hex => [c2 [Hc2 [c1 [Hs [Hi1 Hq]]]]].
    exists c1.
    split; last lia.
    apply/HFmem.
    split=> //.
    split=> //.
    by exists c2.
  } have Hnbf : ZInterval.non_bottomb F
    by apply/non_bottombP; apply/non_bottom_non_empty; move: HexF => [c [Hc _]]; exists c.
  rewrite /interval_quot_dividend_from_divisor_half Hnbf.
  (* [F]'s low bound is the divisor solver's, [≥ 1], so the unsplit solve
     step is the split one — which is the form the blocks below are stated
     on.
   *)
  have [vp [hp [Hvp Hp]]] := interval_quot_solve_divisor_pos_low i2 i0.
  have Hpfst : fst (interval_quot_solve_divisor_pos i2 i0) = WithTop.NotTop vp by rewrite Hp.
  have [l0 [Hl0 Hfst]] := itv_meet_low_ge i1 _ vp Hpfst.
  rewrite -(interval_quot_solve_dividend_split_pos_preclamped F i0 l0 Hfst (ltac:(lia))).
  (* the solve set over γF, and its blocks *)
  have Hb : IsAlpha (A:=itv) (interval_quot_solve_dividend_split F i0)
      (collecting_quot_solve_left (γ[itv] F) (γ[itv] i0))
    by apply: interval_quot_solve_dividend_split_best => //;
      [ move: Hnb0 => /non_bottom_non_empty | exact: non_bottom_is_alpha_gamma ].
  apply: (is_alpha_set_equiv _ _ _ _
    (itv_meet_is_alpha_covered i2 (interval_quot_solve_dividend_split F i0)
      (collecting_quot_solve_left (γ[itv] F) (γ[itv] i0)) (γ[itv] F)
      (fun k => quot_window i0 k) Hb _ _ _)).
  - (* the two set descriptions agree *) split=> c2 Hc2; unfold_set in Hc2; unfold_set.
    + move: Hc2 => [Hi2 Hsolve].
      unfold_set in Hsolve.
      move: Hsolve => [c1 [c0 [HcF [Hc0 [Hne Heq]]]]].
      have [Hs [Hi1 _]] := proj1 (HFmem c1) HcF.
      by split=> //; exists c1; split=> //; split=> //; rewrite Heq.
    + move: Hc2 => [Hi2 [c1 [Hs [Hi1 Hq]]]].
      split=> //.
      unfold_set.
      exists c1, (Z.quot c2 c1).
      split; first by apply/HFmem; split=> //; split=> //; exists c2.
      split; first exact: Hq.
      split; last done.
      by rewrite /is_nonzero; lia.
  - (* the solve set is covered by the blocks *) split=> c2 Hc2; unfold_set in Hc2; unfold_set.
    + move: Hc2 => [c1 [c0 [HcF [Hc0 [Hne Heq]]]]].
      have [Hs _] := proj1 (HFmem c1) HcF.
      exists c1.
      split=> //.
      apply/(quot_window_iff i0 c1 c2 Hs).
      by rewrite Heq.
    + move: Hc2 => [c1 [HcF Hw]].
      have [Hs _] := proj1 (HFmem c1) HcF.
      exists c1, (Z.quot c2 c1).
      split; first exact: HcF.
      split; first by apply/(quot_window_iff i0 c1 c2 Hs).
      split; last done.
      by rewrite /is_nonzero; lia.
  - (* every block meets γ i2 — that is what feasible means *) move=> k HkF.
    have [Hs [_ [c2 [Hc2 Hq]]]] := proj1 (HFmem k) HkF.
    exists c2.
    split=> //.
    by apply/(quot_window_iff i0 k c2 Hs).
  - (* nonempty *) move: Hex => [c2 [Hc2 [c1 [Hs [Hi1 Hq]]]]].
    exists c2.
    split=> //.
    unfold_set.
    exists c1, (Z.quot c2 c1).
    split; first by apply/HFmem; split=> //; split=> //; exists c2.
    split; first exact: Hq.
    split; last done.
    by rewrite /is_nonzero; lia.
Qed.

(**
    The negative half, by the same argument on negated blocks: for [b < 0] the
    dividends landing in [γ i0] are those landing in [γ (-i0)] under division
    by [-b], which is a block again.
 *)
Lemma quot_window_iff_neg (i0 : interval) (b c2 : Z) :
  b < 0 -> (Z.quot c2 b ∈ γ[itv] i0 <-> c2 ∈ γ[itv] (quot_window (interval_opp i0) (- b))).

Proof.
  move=> Hb.
  rewrite -(quot_window_iff (interval_opp i0) (- b) c2 ltac:(lia)).
  rewrite gamma_interval_opp.
  have -> : - Z.quot c2 (- b) = Z.quot c2 b by rewrite (Z.quot_opp_r c2 b ltac:(lia)); lia.
  by [].
Qed.

Lemma quot_dividend_F_neg_exact (i2 i1 i0 : interval) :
  non_bottom i2 -> non_bottom i0 ->
  γ[itv] (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0)) ⊆⊇
  (collecting_quot_backward_right (γ[itv] i2) (γ[itv] i1) (γ[itv] i0))
    ∩ {[ c1 : Z | c1 < 0 ]}.

Proof.
  move=> Hnb2 Hnb0.
  have [ln [vn [Hvn Hn]]] := interval_quot_solve_divisor_neg_high i2 i0.
  have Hsnd : snd (interval_quot_solve_divisor_neg i2 i0) = WithTop.NotTop vn by rewrite Hn.
  rewrite -(itv_meet_strictly_negative_part_absorb i1 _ vn Hsnd Hvn).
  exact: interval_quot_solve_divisor_neg_half_exact.
Qed.

Lemma interval_quot_dividend_from_divisor_half_neg_is_alpha (i2 i1 i0 : interval) :
  non_bottom i2 -> non_bottom i0 ->
  (exists c2, c2 ∈ γ[itv] i2 /\ exists c1,
     c1 < 0 /\ c1 ∈ γ[itv] i1 /\ Z.quot c2 c1 ∈ γ[itv] i0) ->
  IsAlpha (A:=itv)
    (interval_quot_dividend_from_divisor_half i2
       (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0)) i0)
    {[ c2 | c2 ∈ γ[itv] i2 /\ exists c1,
        c1 < 0 /\ c1 ∈ γ[itv] i1 /\ Z.quot c2 c1 ∈ γ[itv] i0 ]}.

Proof.
  move=> Hnb2 Hnb0 Hex.
  have HF := quot_dividend_F_neg_exact i2 i1 i0 Hnb2 Hnb0.
  set F := ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0).
  have HFmem : forall c1,
      c1 ∈ γ[itv] F <->
      (c1 < 0 /\ c1 ∈ γ[itv] i1 /\ exists c2, c2 ∈ γ[itv] i2 /\ Z.quot c2 c1 ∈ γ[itv] i0).
  { move=> c1; split.
    - move=> /(proj1 HF) Hc.
      unfold_set in Hc.
      move: Hc => [Hbw Hsign].
      move: Hbw => /backward_divisor_memE [_ [Hi1 [c2 [Hc2 Hq]]]].
      by split; [exact: Hsign | split=> //; exists c2].
    - move=> [Hs [Hi1 [c2 [Hc2 Hq]]]].
      apply: (proj2 HF).
      unfold_set.
      split=> //.
      by apply/backward_divisor_memE; split; [lia | split=> //; exists c2].
  } have HexF : exists c, c ∈ γ[itv] F /\ c <> 0.
  { move: Hex => [c2 [Hc2 [c1 [Hs [Hi1 Hq]]]]].
    exists c1.
    split; last lia.
    apply/HFmem.
    split=> //.
    split=> //.
    by exists c2.
  } have Hnbf : ZInterval.non_bottomb F
    by apply/non_bottombP; apply/non_bottom_non_empty; move: HexF => [c [Hc _]]; exists c.
  rewrite /interval_quot_dividend_from_divisor_half Hnbf.
  (* [F]'s high bound is the divisor solver's, [≤ -1] — the mirror of the
     positive half's clamp, and the same bridge to the split form.
   *)
  have [ln [vn [Hvn Hn]]] := interval_quot_solve_divisor_neg_high i2 i0.
  have Hnsnd : snd (interval_quot_solve_divisor_neg i2 i0) = WithTop.NotTop vn by rewrite Hn.
  have [h0 [Hh0 Hsnd]] := itv_meet_high_le i1 _ vn Hnsnd.
  have HnbF : non_bottom F by apply/non_bottombP; exact: Hnbf.
  rewrite -(interval_quot_solve_dividend_split_neg_preclamped F i0 h0 Hsnd (ltac:(lia)) HnbF).
  have Hb : IsAlpha (A:=itv) (interval_quot_solve_dividend_split F i0)
      (collecting_quot_solve_left (γ[itv] F) (γ[itv] i0))
    by apply: interval_quot_solve_dividend_split_best => //;
      [ move: Hnb0 => /non_bottom_non_empty | exact: non_bottom_is_alpha_gamma ].
  apply: (is_alpha_set_equiv _ _ _ _
    (itv_meet_is_alpha_covered i2 (interval_quot_solve_dividend_split F i0)
      (collecting_quot_solve_left (γ[itv] F) (γ[itv] i0)) (γ[itv] F)
      (fun k => quot_window (interval_opp i0) (- k)) Hb _ _ _)).
  - split=> c2 Hc2; unfold_set in Hc2; unfold_set.
    + move: Hc2 => [Hi2 Hsolve].
      unfold_set in Hsolve.
      move: Hsolve => [c1 [c0 [HcF [Hc0 [Hne Heq]]]]].
      have [Hs [Hi1 _]] := proj1 (HFmem c1) HcF.
      by split=> //; exists c1; split=> //; split=> //; rewrite Heq.
    + move: Hc2 => [Hi2 [c1 [Hs [Hi1 Hq]]]].
      split=> //.
      unfold_set.
      exists c1, (Z.quot c2 c1).
      split; first by apply/HFmem; split=> //; split=> //; exists c2.
      split; first exact: Hq.
      split; last done.
      by rewrite /is_nonzero; lia.
  - split=> c2 Hc2; unfold_set in Hc2; unfold_set.
    + move: Hc2 => [c1 [c0 [HcF [Hc0 [Hne Heq]]]]].
      have [Hs _] := proj1 (HFmem c1) HcF.
      exists c1.
      split=> //.
      apply/(quot_window_iff_neg i0 c1 c2 Hs).
      by rewrite Heq.
    + move: Hc2 => [c1 [HcF Hw]].
      have [Hs _] := proj1 (HFmem c1) HcF.
      exists c1, (Z.quot c2 c1).
      split; first exact: HcF.
      split; first by apply/(quot_window_iff_neg i0 c1 c2 Hs).
      split; last done.
      by rewrite /is_nonzero; lia.
  - move=> k HkF.
    have [Hs [_ [c2 [Hc2 Hq]]]] := proj1 (HFmem k) HkF.
    exists c2.
    split=> //.
    by apply/(quot_window_iff_neg i0 k c2 Hs).
  - move: Hex => [c2 [Hc2 [c1 [Hs [Hi1 Hq]]]]].
    exists c2.
    split=> //.
    unfold_set.
    exists c1, (Z.quot c2 c1).
    split; first by apply/HFmem; split=> //; split=> //; exists c2.
    split; first exact: Hq.
    split; last done.
    by rewrite /is_nonzero; lia.
Qed.

(**
    [join_possibly_bottom_is_alpha_canon] with [IsAlpha] sides instead of
    exactness. The dividend needs this and the divisor did not: a divisor's
    sign half is *exactly* its part of the backward set, but a dividend's is a
    union of blocks with gaps, so only the weaker [IsAlpha] is available.
    [is_alpha_join_split] already takes [IsAlpha], so this is the original
    proof with its [Hside] converter deleted.
 *)
Lemma is_alpha_itv_to_canon (a : interval) (S : ℘ Z) :
  IsAlpha (A:=itv) a S -> IsAlpha (A:=itv_canon_ad) a S.

Proof.
  move=> Ha.
  apply/is_alpha_itv_canon_iff.
  split=> //.
  by apply: (proj2 (Ha _)); reflexivity.
Qed.

Lemma join_possibly_bottom_is_alpha_canon_gen (a b : interval) (S Sa Sb : ℘ Z) :
  S ⊆⊇ Sa ∪ Sb -> IsAlpha (A:=itv_canon_ad) a Sa ->
  IsAlpha (A:=itv_canon_ad) b Sb ->
  IsAlpha (A:=itv_canon_ad) (join_possibly_bottom a b) S.

Proof.
  move=> HS Ha Hb.
  rewrite -itv_canon_join_eq.
  exact: (is_alpha_join_split itv_canon_ajsl _ _ _ _ _ HS Ha Hb).
Qed.

(**
    ** The dividend is best.

    The two sign halves partition the backward set (the guard rules [0] out),
    each is α of its part, and [join_possibly_bottom] does the rest.
 *)

Lemma backward_dividend_memE (S2 S1 S0 : ℘ Z) (c2 : Z) :
  c2 ∈ collecting_quot_backward_left S2 S1 S0 <->
  c2 ∈ S2 /\ exists c1, c1 <> 0 /\ c1 ∈ S1 /\ Z.quot c2 c1 ∈ S0.

Proof.
  split.
  - move=> H.
    unfold_set in H.
    move: H => [c1 [c0 [Hi2 [Hc1 [Hc0 [Hne Heq]]]]]].
    rewrite /is_nonzero in Hne.
    by split=> //; exists c1; split=> //; split=> //; rewrite Heq.
  - move=> [Hi2 [c1 [Hnz [Hi1 Hq]]]].
    unfold_set.
    by exists c1, (Z.quot c2 c1); do 4 (split=> //).
Qed.

(**
    A dropped half is γ-empty, which is what lets the [classify] dispatch skip
    it and what makes the empty case of the join go through.
 *)
Lemma interval_quot_dividend_from_divisor_half_bottom (i2 F i0 : interval) :
  ZInterval.non_bottomb F = false ->
  ZInterval.non_bottomb (interval_quot_dividend_from_divisor_half i2 F i0) = false.

Proof.
  move=> HF.
  rewrite /interval_quot_dividend_from_divisor_half HF.
  by move: i2 => [[|l] [|h]] /=; apply/Z.leb_gt; lia.
Qed.

Lemma is_alpha_canon_of_bottom (a : interval) (S : ℘ Z) :
  ZInterval.non_bottomb a = false -> (forall c, c ∈ S -> False) ->
  IsAlpha (A:=itv_canon_ad) a S.

Proof.
  move=> Ha HS.
  apply/is_alpha_itv_canon_iff.
  split.
  - move=> c Hc.
    by exfalso; exact: HS c Hc.
  - by rewrite Ha.
Qed.

Lemma quot_dividend_jpb_is_alpha (i2 i1 i0 : interval) :
  non_bottom i2 -> non_bottom i0 ->
  IsAlpha (A:=itv_canon_ad)
    (ZInterval.join_possibly_bottom
       (interval_quot_dividend_from_divisor_half i2
          (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0)) i0)
       (interval_quot_dividend_from_divisor_half i2
          (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0)) i0))
    (collecting_quot_backward_left (γ[itv] i2) (γ[itv] i1) (γ[itv] i0)).

Proof.
  move=> Hnb2 Hnb0.
  have HFn := quot_dividend_F_neg_exact i2 i1 i0 Hnb2 Hnb0.
  have HFp := quot_dividend_F_pos_exact i2 i1 i0 Hnb2 Hnb0.
  apply: (join_possibly_bottom_is_alpha_canon_gen _ _ _
    {[ c2 | c2 ∈ γ[itv] i2 /\ exists c1, c1 < 0 /\ c1 ∈ γ[itv] i1 /\ Z.quot c2 c1 ∈ γ[itv] i0 ]}
    {[ c2 | c2 ∈ γ[itv] i2 /\ exists c1, 0 < c1 /\ c1 ∈ γ[itv] i1 /\ Z.quot c2 c1 ∈ γ[itv] i0 ]}).
  - split=> c2 Hc2.
    + move: Hc2 => /backward_dividend_memE [Hi2 [c1 [Hnz [Hi1 Hq]]]].
      unfold_set.
      case: (Z.lt_ge_cases c1 0) => Hs;
        [left|right]; unfold_set; split=> //; exists c1; split; by [lia | split].
    + unfold_set in Hc2.
      apply/backward_dividend_memE.
      case: Hc2 => Hc2; unfold_set in Hc2;
        move: Hc2 => [Hi2 [c1 [Hs [Hi1 Hq]]]]; by split=> //; exists c1; split; [lia | split].
  - (* negative half *)
    case Hnb: (ZInterval.non_bottomb (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0))).
    + apply: is_alpha_itv_to_canon.
      apply: interval_quot_dividend_from_divisor_half_neg_is_alpha => //.
      have [c1 Hc1] : exists c,
          c ∈ γ[itv] (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0))
        by apply/non_bottom_non_empty; apply/non_bottombP; rewrite Hnb.
      move: (proj1 HFn c1 Hc1) => Hc.
      unfold_set in Hc.
      move: Hc => [Hbw Hsign].
      move: Hbw => /backward_divisor_memE [_ [Hi1 [c2 [Hc2 Hq]]]].
      by exists c2; split=> //; exists c1; split=> //; split.
   + apply: is_alpha_canon_of_bottom; first exact: interval_quot_dividend_from_divisor_half_bottom.
     move=> c Hc.
     unfold_set in Hc.
     move: Hc => [Hi2 [c1 [Hs [Hi1 Hq]]]].
     have Hin : c1 ∈ γ[itv] (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0)).
     { apply: (proj2 HFn).
       unfold_set.
       split=> //.
       by apply/backward_divisor_memE; split; [lia | split=> //; exists c].
     } have : ZInterval.non_bottomb (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0))
       by apply/non_bottombP; apply/non_bottom_non_empty; exists c1.
     by rewrite Hnb.
  - (* positive half *)
    case Hnb: (ZInterval.non_bottomb (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0))).
    + apply: is_alpha_itv_to_canon.
      apply: interval_quot_dividend_from_divisor_half_pos_is_alpha => //.
      have [c1 Hc1] : exists c,
          c ∈ γ[itv] (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0))
        by apply/non_bottom_non_empty; apply/non_bottombP; rewrite Hnb.
      move: (proj1 HFp c1 Hc1) => Hc.
      unfold_set in Hc.
      move: Hc => [Hbw Hsign].
      move: Hbw => /backward_divisor_memE [_ [Hi1 [c2 [Hc2 Hq]]]].
      by exists c2; split=> //; exists c1; split=> //; split.
    + apply: is_alpha_canon_of_bottom; first exact: interval_quot_dividend_from_divisor_half_bottom.
      move=> c Hc.
      unfold_set in Hc.
      move: Hc => [Hi2 [c1 [Hs [Hi1 Hq]]]].
      have Hin : c1 ∈ γ[itv] (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0)).
      { apply: (proj2 HFp).
        unfold_set.
        split=> //.
        by apply/backward_divisor_memE; split; [lia | split=> //; exists c].
      } have : ZInterval.non_bottomb (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0))
        by apply/non_bottombP; apply/non_bottom_non_empty; exists c1.
      by rewrite Hnb.
Qed.

(**
    The [classify] dispatch against the plain join, exactly as on the divisor
    side and with the same single corner: when both halves are γ-empty the
    left-biased [join_possibly_bottom] reports the positive half's bounds
    where the [Neg] branch reports the negative half's. Both are ⊥.
 *)
Lemma interval_quot_dividend_refine_gamma_eq (i2 i1 i0 : interval) :
  γ[itv] (ZInterval.join_possibly_bottom
    (interval_quot_dividend_from_divisor_half i2
      (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0)) i0)
    (interval_quot_dividend_from_divisor_half i2
      (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0)) i0))
  ⊆⊇ γ[itv] (interval_quot_dividend_refine i2 i1 i0).

Proof.
  have [ln [vn [Hvn Hn]]] := interval_quot_solve_divisor_neg_high i2 i0.
  have [vp [hp [Hvp Hp]]] := interval_quot_solve_divisor_pos_low i2 i0.
  rewrite /interval_quot_dividend_refine Hn Hp /ZInterval.join_possibly_bottom.
  case Hc: (classify i1).
  - rewrite (interval_quot_dividend_from_divisor_half_bottom i2 _ i0
      (itv_meet_bottom_of_classify_Pos i1 (ln, WithTop.NotTop vn) vn Hc erefl Hvn)).
    by split.
  - rewrite (interval_quot_dividend_from_divisor_half_bottom i2 _ i0
      (itv_meet_bottom_of_classify_Neg i1 (WithTop.NotTop vp, hp) vp Hc erefl Hvp)).
    case HA: (ZInterval.non_bottomb
      (interval_quot_dividend_from_divisor_half i2 (ZInterval.meet i1 (ln, WithTop.NotTop vn)) i0));
      first by split.
    split=> c Hc'; exfalso.
    + exact: (itv_non_bottomb_false_empty _ c
        (interval_quot_dividend_from_divisor_half_bottom i2 _ i0
          (itv_meet_bottom_of_classify_Neg i1 (WithTop.NotTop vp, hp) vp Hc erefl Hvp)) Hc').
    + exact: (itv_non_bottomb_false_empty _ c HA Hc').
  - by split.
Qed.

(**
    The dividend, best. Unlike the divisor this is *not* reachable by
    sharpening the solve step — the solve set is non-convex and its hull meets
    [i2] too generously. It is reachable by shrinking the *divisor* first, and
    then the covering lemma applies because every surviving block meets [γ
    i2]. See [todo/quot_backward_dividend.md].

    [_best], not [_alpha_complete], and that is a ceiling rather than a
    missing proof: no backward transfer function on intervals can be
    α-complete ([todo/zinterval_backward_gaps.md]).
 *)
Theorem backward_interval_quot_dividend_best :
  ternary_best nbitv nbitv nbitv itv backward_interval_quot_dividend
    collecting_quot_backward_left.

Proof.
  move=> [i2 H2] [i1 H1] [i0 H0].
  rewrite /backward_interval_quot_dividend /=.
  apply: (most_precise_gamma_equiv _ _ _ (interval_quot_dividend_refine_gamma_eq i2 i1 i0)).
  apply: (is_alpha_is_most_precise (A:=itv_canon_ad)).
  exact: quot_dividend_jpb_is_alpha.
Qed.

(**
    Both halves are a meet with [i2] when they are anything at all, so the
    [option] protocol's "never grows the operand" is immediate.
 *)
Lemma backward_interval_quot_dividend_lower_bound (i2 i1 i0 : nb_interval) :
  backward_interval_quot_dividend i2 i1 i0 ⊑[itv] (`i2).

Proof.
  rewrite /backward_interval_quot_dividend /interval_quot_dividend_refine.
  case: (classify (`i1)).
  - rewrite /interval_quot_dividend_from_divisor_half; exact: itv_meet_lower_bound_l.
  - rewrite /interval_quot_dividend_from_divisor_half; exact: itv_meet_lower_bound_l.
  - by apply: join_possibly_bottom_lower_bound;
      rewrite /interval_quot_dividend_from_divisor_half; exact: itv_meet_lower_bound_l.
Qed.

(**
    The shared interface against the composed one. Both components branch on
    the same [classify], and in each branch the shared form is the composed
    one with the two halves named — so this is a case split and nothing else.
 *)
Lemma impl_backward_interval_quot_eq (i2 i1 i0 : nb_interval) :
  impl_backward_interval_quot i2 i1 i0 = impl_backward_interval_quot_unopt i2 i1 i0.

Proof.
  rewrite /impl_backward_interval_quot /impl_backward_interval_quot_unopt /impl_backward_itv
    /backward_interval_quot_dividend /interval_quot_dividend_refine
    /backward_interval_quot_divisor /interval_quot_solve_divisor_split.
  by case: (classify (`i1)).
Qed.

Lemma impl_backward_interval_quot_correct :
  backward_itv_correct impl_backward_interval_quot backward_interval_quot_dividend
    backward_interval_quot_divisor.

Proof.
  move=> i2 i1 i0.
  rewrite impl_backward_interval_quot_eq.
  exact: (impl_backward_itv_correct backward_interval_quot_dividend backward_interval_quot_divisor
    backward_interval_quot_dividend_lower_bound backward_interval_quot_divisor_lower_bound
    i2 i1 i0).
Qed.


(**
    * The interface at work.
 *)

Local Notation N := WithTop.NotTop.

(**
    The operands' non-bottomness is part of their type, so the examples below
    have to supply it. [nb i] is [i] with that proof found by [lia] (or by
    [done], for the [Top] bounds where [non_bottom] is [True]).
 *)
Local Definition nbI (i : interval) (H : non_bottom i) : nb_interval := exist _ i H.
Local Notation nb i := (nbI i ltac:(by simpl; try lia)) (only parsing).

(**
    [x ÷ 3 = 5]. Exact: the sign-aware window knows the remainder of a
    positive dividend is non-negative, so [x] cannot be below [15].
 *)
Example backward_quot_bounds_dividend :
  impl_backward_interval_quot (nb itv_top) (nb (N 3, N 3)) (nb (N 5, N 5)) =
  (Some (N 15, N 17), None).

Proof.
  reflexivity.
Qed.

(**
    …and symmetrically below zero: [x ÷ 3 = -5] gives [[-17,-15]].
 *)
Example backward_quot_bounds_dividend_neg :
  impl_backward_interval_quot (nb itv_top) (nb (N 3, N 3)) (nb (N (-5), N (-5))) =
  (Some (N (-17), N (-15)), None).

Proof.
  reflexivity.
Qed.

(**
    A zero quotient is the one case where the remainder may have either sign,
    so the window stays symmetric — and is still exact.
 *)
Example backward_quot_zero_quotient :
  impl_backward_interval_quot (nb itv_top) (nb (N 3, N 3)) (nb (N 0, N 0)) =
  (Some (N (-2), N 2), None).

Proof.
  reflexivity.
Qed.

(**
    The fact an analyzer wants out of a division: the divisor is not zero.
    Here [y ∈ [0,4]] becomes [y ∈ [1,4]] — and the dividend gets the benefit
    of the same clamp, since [x ÷ y = 5] with [y ≥ 1] puts [x] at [5] or
    above. Before the clamp the answer was [[0,23]].
 *)
Example backward_quot_divisor_nonzero :
  impl_backward_interval_quot (nb itv_top) (nb (N 0, N 4)) (nb (N 5, N 5)) =
  (Some (N 5, N 23), Some (N 1, N 4)).

Proof.
  reflexivity.
Qed.

(**
    The divisor, exactly: [100 ÷ y = 3] holds for [y ∈ [26,33]] and for no
    other [y] of either sign. The upper bound is [100 ÷ 3]; the lower one is
    [100 ÷ 4 + 1], the divisor one step past the quotient. The negative half
    is γ-empty — a positive dividend and a positive quotient force a positive
    divisor — and the join drops it.
 *)
Example backward_quot_bounds_divisor :
  impl_backward_interval_quot (nb (N 100, N 100)) (nb itv_top) (nb (N 3, N 3)) =
  (None, Some (N 26, N 33)).

Proof.
  reflexivity.
Qed.

(**
    Both facts at once, on the negative side, and here the constraint is
    settled outright on *both* operands: a non-negative dividend divided by a
    divisor at most [-1] cannot give [5]. The dividend refines to a γ-empty
    interval, and so does the divisor — both sign halves come out empty, so
    the join has nothing to return but a contradiction. The magnitude bound
    used to answer [[-20,-1]] here, which is sound but says nothing.

    Which γ-empty pair the divisor comes back as is the one place where the
    extracted [interval_quot_solve_divisor_split] and the [_unopt] it is
    proved against part company
    ([interval_quot_solve_divisor_split_gamma_eq]): this divisor classifies
    [Neg], so the dispatch reports the negative half's [(0, -1)] where the
    left-biased [join_possibly_bottom] reported the positive half's [(1, 0)].
    Both are ⊥.
 *)
Example backward_quot_divisor_nonzero_neg :
  impl_backward_interval_quot (nb (N 0, N 100)) (nb ((WithTop.Top, N 0) : interval))
    (nb (N 5, N 5)) = (Some (N 1, N 0), Some (N 0, N (-1))).

Proof.
  reflexivity.
Qed.

(**
    A divisor that strictly straddles [0] cannot have the [0] removed — "≠ 0"
    is not an interval — but that is no longer the end of it: the solve step
    still rules out the negative half and caps the positive one, so [x ÷ y =
    5] with [x ∈ [0,100]] refines [y ∈ [-2,2]] to [[1,2]].

    The dividend then benefits from that same refinement: only [y ∈ {1,2}]
    survives, giving [x ∈ {5} ∪ [10,11]] and so [[5,11]]. Solving against the
    *incoming* [y ∈ [-2,2]] answered [[0,11]].
 *)
Example backward_quot_divisor_straddling_zero :
  impl_backward_interval_quot (nb (N 0, N 100)) (nb (N (-2), N 2)) (nb (N 5, N 5)) =
  (Some (N 5, N 11), Some (N 1, N 2)).

Proof.
  reflexivity.
Qed.

(**
    The gap between two blocks. [x ÷ y = 5] with [y ∈ [2,3]] admits [x ∈
    [10,11] ∪ [15,17]], and [x ∈ [12,16]] meets only the second block — but
    the *hull* of the two blocks is [[10,17]], so meeting that with [[12,16]]
    would answer [[12,16]] and learn nothing. Refining the divisor first
    collapses it to [y = 3], whose single block gives the exact [[15,16]].
    This is the case the dividend used to get wrong.
 *)
Example backward_quot_dividend_block_gap :
  impl_backward_interval_quot (nb (N 12, N 16)) (nb (N 2, N 3)) (nb (N 5, N 5)) =
  (Some (N 15, N 16), Some (N 3, N 3)).

Proof.
  reflexivity.
Qed.

(**
    Nothing to learn.
 *)
Example backward_quot_learns_nothing :
  impl_backward_interval_quot (nb (N 0, N 10)) (nb (N 1, N 1)) (nb (N 0, N 10)) =
  (None, None).

Proof.
  reflexivity.
Qed.


(**
    * Precision of the divisor: not α-complete, on any quadrant.

    The *dividend* is α-complete on a sign-definite divisor
    ([interval_quot_solve_dividend_{pos,neg}_alpha_complete]): arbitrary
    operand sets, tied to the intervals only by [IsAlpha]. The *divisor* is
    not, and the witness below shows it is not a matter of finding the right
    sign case — every operand in it is strictly positive.

    The difference is structural. On the dividend side the solve set is an
    **image**: [c2] ranges over [c0 * c1] widened by the remainder, and both
    extremes of that image are attained at extremes of the operands, which is
    exactly what [IsAlpha] of the operand sets records. On the divisor side
    the answer is a **feasibility**: [c1] survives iff *some pair* [(c2, c0) ∈
    S2 × S0] has [c2 ÷ c1 = c0]. A hole in either operand set kills a divisor
    without moving either hull, and no interval can see it.

    Here the hole is in [S0 = {1,3}]. Its best abstraction [[1,3]] contains
    [2], and [2 ÷ 1 = 2] makes the divisor [1] look feasible — it is not,
    since [2 ∉ S0]. Only [2 ÷ 2 = 1] is, so the backward set is [{2}] and the
    best abstraction is [[2,2]] against the computed [[1,2]].

    Not a corner case: over subsets of [[-6,6]] with both operands
    sign-definite, 20 559 of 361 179 triples fail, the same count in each
    quadrant. What survives is bestness at γ, where the operands *are*
    intervals and the holes cannot arise; the same brute force finds that
    exact on every box ([todo/quot_backward_divisor.md] §5).
 *)

Section Alpha_incompleteness.

  Local Definition S2 : ℘ Z := {[ z | z = 2 ]}.
  Local Definition S1 : ℘ Z := {[ z | z = 1 \/ z = 2 ]}.
  Local Definition S0 : ℘ Z := {[ z | z = 1 \/ z = 3 ]}.

  Local Lemma alpha_S2 : IsAlpha (A:=itv) (N 2, N 2) S2.

  Proof.
    apply: is_alpha_itv_attained; rewrite /S2; unfold_set; lia.
  Qed.

  Local Lemma alpha_S1 : IsAlpha (A:=itv) (N 1, N 2) S1.

  Proof.
    apply: is_alpha_itv_attained; rewrite /S1; unfold_set; lia.
  Qed.

  Local Lemma alpha_S0 : IsAlpha (A:=itv) (N 1, N 3) S0.

  Proof.
    apply: is_alpha_itv_attained; rewrite /S0; unfold_set; lia.
  Qed.

(**
    [S1] offers two divisors and only one of them divides [2] into [S0]: [2 ÷
    1 = 2 ∉ S0], [2 ÷ 2 = 1 ∈ S0].
 *)
  Local Lemma backward_set_singleton :
    collecting_quot_backward_right S2 S1 S0 ⊆⊇ {[ z | z = 2 ]}.

  Proof.
    unfold_set_equiv => c1; unfold_set; split.
    - move=> [c2 [c0 [Hc2 [Hc1 [Hc0 [_ Heq]]]]]].
      move: Hc2 Hc1 Hc0 Heq.
      rewrite /S2 /S1 /S0.
      unfold_set.
      by move=> -> [->|->] [->|->].
    - move=> ->.
      exists 2, 1.
      rewrite /S2 /S1 /S0.
      unfold_set.
      by repeat split; auto.
  Qed.

(**
    The best abstraction of [{2}] is [[2,2]]; the transfer function returns
    [[1,2]], which is not [⊑] it.
 *)
  Example backward_quot_divisor_not_alpha_complete :
    ~ (forall (i2 i1 i0 : nb_interval) (T2 T1 T0 : ℘ Z),
        IsAlpha (A:=itv) (`i2) T2 -> IsAlpha (A:=itv) (`i1) T1 -> IsAlpha (A:=itv) (`i0) T0 ->
        IsAlpha (A:=itv) (backward_interval_quot_divisor i2 i1 i0)
          (collecting_quot_backward_right T2 T1 T0)).

  Proof.
    move=> Hac.
    have H := Hac (nb (N 2, N 2)) (nb (N 1, N 2)) (nb (N 1, N 3)) _ _ _ alpha_S2 alpha_S1 alpha_S0.
    move: H => /(is_alpha_set_equiv _ _ _ backward_set_singleton) H.
    (* [backward_interval_quot_divisor] computes [[1,2]] here, and [[1,2]] is
       not included in [[2,2]] — while [{2}] is.
     *)
    have Hsub : {[ z : Z | z = 2 ]} ⊆ γ[itv] (N 2, N 2).
    { move=> c Hc.
      unfold_set in Hc.
      subst.
      by unfold_set; lia.
    } have := proj1 (H (N 2, N 2)) Hsub.
    by move=> /is_includedP.
  Qed.

End Alpha_incompleteness.

