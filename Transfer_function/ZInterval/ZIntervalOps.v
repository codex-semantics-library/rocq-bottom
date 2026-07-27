(* ZIntervalOps.v - Computational transfer functions for the ZInterval
   single-value abstraction. This is the executable core, destined to be
   extracted 1:1 to OCaml. Their proofs are in the matching [*Theory.v]
   files of this directory.

   STATUS: opp (OppTheory), add, sub (AddTheory), mul (MulTheory),
   quot (QuotTheory), le (LeTheory), eqb (EqbTheory);
   backward add, sub (AddBackwardTheory), backward mul
   (MulBackwardTheory), backward quot (QuotBackwardTheory). *)

From Stdlib Require Import ZArith.
Require Import
  Abstraction AbstractionCombination
  Quadrivalent
  ZInterval.

Open Scope Z_scope.

(** * Z.opp. See [OppTheory.v]. *)

Definition neg_bound (b : WithTop.with_top Z) : WithTop.with_top Z :=
  match b with WithTop.Top => WithTop.Top | WithTop.NotTop z => WithTop.NotTop (-z) end.

Definition interval_opp (i : interval) : interval :=
  let (l, h) := i in (neg_bound h, neg_bound l).

(** * Z.add and Z.sub. See [AddTheory.v]. *)

Definition interval_add (i2 i1: interval) : interval :=
  let (l2,h2) := i2 in
  let (l1,h1) := i1 in
  (WithTop.lift2 Z.add l2 l1, WithTop.lift2 Z.add h2 h1).

(** Direct definition for efficient extraction. Equivalent to
    interval_add i1 (interval_opp i2), proved below. *)

Definition sub_bound (a b : WithTop.with_top Z) : WithTop.with_top Z :=
  match a, b with
  | WithTop.Top, _ | _, WithTop.Top => WithTop.Top
  | WithTop.NotTop a, WithTop.NotTop b => WithTop.NotTop (a - b)
  end.

Definition interval_sub (i1 i2 : interval) : interval :=
  let (l1,h1) := i1 in
  let (l2,h2) := i2 in
  (sub_bound l1 h2, sub_bound h1 l2).

(** * Backward [Z.add] and [Z.sub]. See [AddBackwardTheory.v].

    Both [Z.add] and [Z.sub] are invertible in each argument, so in
    every case the backward transfer function is "meet the incoming
    interval with the forward image of the inverse":

<<
      c2 + c1 = c0   <->   c0 - c1 = c2   <->   c0 - c2 = c1
      c2 - c1 = c0   <->   c0 + c1 = c2   <->   c2 - c0 = c1
>>

    Note the argument order of the [_right] case of [sub]: the inverse
    is [fun c0 c2 => c2 - c0], not [Z.sub]. *)

Definition backward_interval_add_left (i2 i1 i0 : interval) : interval :=
  ZInterval.meet i2 (interval_sub i0 i1).

Definition backward_interval_add_right (i2 i1 i0 : interval) : interval :=
  ZInterval.meet i1 (interval_sub i0 i2).

Definition backward_interval_sub_left (i2 i1 i0 : interval) : interval :=
  ZInterval.meet i2 (interval_add i0 i1).

Definition backward_interval_sub_right (i2 i1 i0 : interval) : interval :=
  ZInterval.meet i1 (interval_sub i2 i0).

(** ** Low-level refinement interface.

    Both operands are refined in one call, and each result is reported
    as [None] ("nothing learned, keep the incoming interval") or
    [Some i'] ("refined to [i']").

    Since both components are just a meet, returning both at once needs
    no extra reasoning: it is the pair of the two independent meets. *)

Definition refine_itv (old new : interval) : option interval :=
  if ZInterval.equiv new old then None else Some new.

Definition impl_backward_interval_add (i2 i1 i0 : interval)
  : option interval * option interval :=
  (refine_itv i2 (backward_interval_add_left  i2 i1 i0),
   refine_itv i1 (backward_interval_add_right i2 i1 i0)).

Definition impl_backward_interval_sub (i2 i1 i0 : interval)
  : option interval * option interval :=
  (refine_itv i2 (backward_interval_sub_left  i2 i1 i0),
   refine_itv i1 (backward_interval_sub_right i2 i1 i0)).

(** * Z.mul. See [MulTheory.v]. *)

Definition bound_mul a b :=
  match a, b with
  | WithTop.NotTop 0, _ | _, WithTop.NotTop 0 => WithTop.NotTop 0
  | WithTop.NotTop x, WithTop.NotTop y => WithTop.NotTop (x * y)
  | _,_ => WithTop.Top
  end.

Definition interval_mul_opt (i2 i1: interval) : interval :=
  let (l1,h1) := i1 in
  let (l2,h2) := i2 in
  let m := bound_mul in
  match classify i1, classify i2 with
  | Pos, Pos => (m l1 l2, m h1 h2)
  | Neg, Neg => (m h1 h2, m l1 l2)
  | Pos, Neg => (m h1 l2, m l1 h2)
  | Neg, Pos => (m l1 h2, m h1 l2)
  | Pos, Across => (m h1 l2, m h1 h2)
  | Across, Pos => (m l1 h2, m h1 h2)
  | Neg, Across => (m l1 h2, m l1 l2)
  | Across, Neg => (m h1 l2, m l1 l2)
  | Across, Across => ZInterval.join (m l1 h2, m l1 l2) (m h1 l2, m h1 h2)
  end.

(** * Z.quot. See [QuotTheory.v]. *)

(** Division bound: a / b with Top handling.
  Top / b = Top (unbounded dividend -> unbounded quotient)
  a / Top = 0  (finite dividend / unbounded divisor -> 0) *)
Definition quot_bound (a b : WithTop.with_top Z) : WithTop.with_top Z :=
  match a, b with
  | _, WithTop.Top => WithTop.NotTop 0
  | WithTop.Top, _ => WithTop.Top
  | WithTop.NotTop a, WithTop.NotTop b => WithTop.NotTop (Z.quot a b)
  end.

(** For positive dividend [l1,h1] and strictly positive divisor [l2,h2]:
  result = [l1/h2, h1/l2]. *)
Definition interval_quot_pos (i1 i2 : interval) : interval :=
  let (l1, h1) := i1 in
  let (l2, h2) := i2 in
  (quot_bound l1 h2, quot_bound h1 l2).

(** Quarter functions: both dividend and divisor have definite sign. *)

Definition interval_quot_neg_pos (i2 i1 : interval) : interval :=
  interval_opp (interval_quot_pos (interval_opp i2) i1).

Definition interval_quot_pos_neg (i2 i1 : interval) : interval :=
  interval_opp (interval_quot_pos i2 (interval_opp i1)).

Definition interval_quot_neg_neg (i2 i1 : interval) : interval :=
  interval_quot_pos (interval_opp i2) (interval_opp i1).

(** Across-dividend functions: dividend crosses zero, divisor has definite sign.
    Split the dividend at 0. *)

Definition interval_quot_across_pos (i2 i1 : interval) : interval :=
  ZInterval.join
    (interval_quot_neg_pos (fst i2, WithTop.NotTop 0) i1)
    (interval_quot_pos (WithTop.NotTop 0, snd i2) i1).

Definition interval_quot_across_neg (i2 i1 : interval) : interval :=
  ZInterval.join
    (interval_quot_neg_neg (fst i2, WithTop.NotTop 0) i1)
    (interval_quot_pos_neg (WithTop.NotTop 0, snd i2) i1).

(** Across-divisor functions: divisor crosses zero.
    Split the divisor into [l1, -1] and [1, h1], excluding 0. *)

Definition interval_quot_pos_across (i2 i1 : interval) : interval :=
  let (l1, h1) := i1 in
  ZInterval.join
    (interval_quot_pos_neg i2 (l1, WithTop.NotTop (-1)))
    (interval_quot_pos i2 (WithTop.NotTop 1, h1)).

Definition interval_quot_neg_across (i2 i1 : interval) : interval :=
  let (l1, h1) := i1 in
  ZInterval.join
    (interval_quot_neg_neg i2 (l1, WithTop.NotTop (-1)))
    (interval_quot_neg_pos i2 (WithTop.NotTop 1, h1)).

(** Optimized across-divisor functions (moved here so across_across can use them). *)
Definition interval_quot_pos_across_opt (i2 i1 : interval) : interval :=
  let (_, h2) := i2 in (neg_bound h2, h2).

Definition interval_quot_neg_across_opt (i2 i1 : interval) : interval :=
  let (l2, _) := i2 in (l2, neg_bound l2).

Definition interval_quot_across_across (i2 i1 : interval) : interval :=
  let (l2, h2) := i2 in
  ZInterval.join
    (interval_quot_neg_across_opt (l2, WithTop.NotTop 0) i1)
    (interval_quot_pos_across_opt (WithTop.NotTop 0, h2) i1).

Definition interval_quot_full (i2 i1 : interval) : interval :=
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
  | DivAcross =>
      match classify i2 with
      | Pos    => interval_quot_pos_across i2 i1
      | Neg    => interval_quot_neg_across i2 i1
      | Across => interval_quot_across_across i2 i1
      end
  end.

(** * Backward [Z.mul]. See [MulBackwardTheory.v].

    [Z.mul] is not invertible, so — unlike backward add/sub — this is
    only a sound over-approximation. Two distinct sources of imprecision:

    - [c2 = 0] annihilates [c1]: if [0] can be both an operand and the
      result, nothing whatsoever can be learned. Dividing regardless
      would be *unsound*, because [interval_quot_full] excludes [0] from
      its divisor (and answers [ZInterval.bottom] on [[0,0]]), so the guard below
      is not an optimisation but a correctness requirement.

    - Divisibility is not expressible: from [2 * c1 = 1] there is no
      solution, but [[1,1] ÷ [2,2] = [0,0]]. (The interval × congruence
      product is the domain that recovers this.) *)

Definition itv_top : interval := (WithTop.Top, WithTop.Top).

(** [0] can be both the operand and the result: then [c2 = 0] admits
    every [c1] and no refinement is possible. *)
Definition mul_solve_unconstrained (i0 i2 : interval) : bool :=
  itv_gammab i2 0 && itv_gammab i0 0.

(** Over-approximates [{c1 | ∃ c2 ∈ γ i2, c0 ∈ γ i0, c2 * c1 = c0}].
    When the guard fails, [c2 ≠ 0] is forced, so [c1 = c0 ÷ c2] exactly
    (the division leaves no remainder) and the verified
    [interval_quot_full] applies. *)
Definition interval_mul_solve (i0 i2 : interval) : interval :=
  if mul_solve_unconstrained i0 i2 then itv_top
  else interval_quot_full i0 i2.

Definition backward_interval_mul_right (i2 i1 i0 : interval) : interval :=
  ZInterval.meet i1 (interval_mul_solve i0 i2).

(** [Z.mul] is commutative, so the left refinement is the right one with
    the operands swapped. *)
Definition backward_interval_mul_left (i2 i1 i0 : interval) : interval :=
  backward_interval_mul_right i1 i2 i0.

Definition impl_backward_interval_mul (i2 i1 i0 : interval)
  : option interval * option interval :=
  (refine_itv i2 (backward_interval_mul_left  i2 i1 i0),
   refine_itv i1 (backward_interval_mul_right i2 i1 i0)).

(** * Backward [Z.quot]. See [QuotBackwardTheory.v].

    The least invertible of the four: many dividends share a quotient,
    and the two arguments behave completely differently.

    - Dividend ([_left]). Truncated division satisfies
      [c2 = c1 * (c2 ÷ c1) + Z.rem c2 c1] with [|Z.rem c2 c1| < |c1|], so
      the dividend lies within [|c1| - 1] of [c0 * c1]. That is a genuine
      refinement, and the useful one.

    - Divisor ([_right]). Two things are learnable. Always: the
      partiality condition [c1 ≠ 0], the fact an analyzer most wants out
      of a division. And when the *quotient* cannot be zero, a magnitude
      bound: [|c1| * |c0| ≤ |c2|], so [|c1| ≤ max|γ i2| ÷ min|γ i0|].
      (What remains out of reach is the exact set of compatible
      divisors, which is not convex: [100 ÷ y = 3] holds for
      [y ∈ {25..33}], and [100 ÷ y = 0] for [|y| > 100].) *)

(** Drop [0] from an interval when the bounds allow it (they do not when
    the interval strictly straddles [0]). Keeps every non-zero member. *)
Definition itv_remove_zero (i : interval) : interval :=
  let (l, h) := i in
  match l, h with
  | WithTop.NotTop Z0, _ => (WithTop.NotTop 1, h)
  | _, WithTop.NotTop Z0 => (l, WithTop.NotTop (-1))
  | _, _ => i
  end.

(** Bounds the remainder [Z.rem c2 c1] by the largest magnitude a
    divisor drawn from [i1] can have. *)
Definition quot_slack (i1 : interval) : interval :=
  match i1 with
  | (WithTop.NotTop l, WithTop.NotTop h) =>
      let m := Z.max (Z.abs l) (Z.abs h) in
      (WithTop.NotTop (1 - m), WithTop.NotTop (m - 1))
  | _ => itv_top
  end.

(** The remainder carries the sign of the dividend, and when the
    quotient is non-zero the dividend carries the sign of [c0 * c1]
    (the remainder is too small to pull it across zero). So whenever
    [0 ∉ γ i0] and the product has a definite sign, the slack is
    one-sided: [c2] lies strictly *away* from zero relative to
    [c0 * c1], never on the near side. This is what makes
    [x ÷ 3 = 5] give the exact [[15,17]] rather than [[13,17]]. *)
Definition quot_slack_signed (i1 i0 : interval) : interval :=
  let s := quot_slack i1 in
  if itv_gammab i0 0 then s
  else match classify (interval_mul_opt i0 i1) with
       | Pos    => (WithTop.NotTop 0, snd s)
       | Neg    => (fst s, WithTop.NotTop 0)
       | Across => s
       end.

Definition interval_quot_solve_left (i1 i0 : interval) : interval :=
  interval_add (interval_mul_opt i0 i1) (quot_slack_signed i1 i0).

Definition backward_interval_quot_left (i2 i1 i0 : interval) : interval :=
  ZInterval.meet i2 (interval_quot_solve_left i1 i0).

(** Magnitude bounds on the members of an interval. [itv_max_abs] is
    [None] when the interval is unbounded; [itv_min_abs] falls back to
    [0] when the interval reaches or straddles zero. *)
Definition itv_max_abs (i : interval) : option Z :=
  match i with
  | (WithTop.NotTop l, WithTop.NotTop h) => Some (Z.max (Z.abs l) (Z.abs h))
  | _ => None
  end.

Definition itv_min_abs (i : interval) : Z :=
  let (l, h) := i in
  let from_h := match h with
                | WithTop.NotTop h' => if h' <? 0 then -h' else 0
                | WithTop.Top => 0
                end in
  match l with
  | WithTop.NotTop l' => if 0 <? l' then l' else from_h
  | WithTop.Top => from_h
  end.

(** Magnitude bound on the divisor, valid when the quotient cannot be
    [0]: from [|c1| * |c0| ≤ |c2|] and [|c0| ≥ itv_min_abs i0]. Degrades
    to [⊤] when the quotient may be [0] (nothing to say: any large enough
    divisor works) or the dividend is unbounded. *)
Definition quot_divisor_bound (i2 i0 : interval) : interval :=
  match itv_max_abs i2 with
  | None => itv_top
  | Some m2 =>
      let m0 := itv_min_abs i0 in
      if 0 <? m0
      then let b := Z.quot m2 m0 in (WithTop.NotTop (- b), WithTop.NotTop b)
      else itv_top
  end.

Definition backward_interval_quot_right (i2 i1 i0 : interval) : interval :=
  itv_remove_zero (ZInterval.meet i1 (quot_divisor_bound i2 i0)).

Definition impl_backward_interval_quot (i2 i1 i0 : interval)
  : option interval * option interval :=
  (refine_itv i2 (backward_interval_quot_left  i2 i1 i0),
   refine_itv i1 (backward_interval_quot_right i2 i1 i0)).

(** * Z.leb. See [LeTheory.v]. *)

(** Whether Z.leb c1 c2 = true is possible: need c1 ≤ c2,
    i.e. the lower bound of i1 ≤ the upper bound of i2. *)
Definition may_be_true_leb (l2 h1 : WithTop.with_top Z) : bool :=
  match l2, h1 with
  | WithTop.Top, _ => true
  | _, WithTop.Top => true
  | WithTop.NotTop l2', WithTop.NotTop h1' => Z.leb l2' h1'
  end.

(** Whether Z.leb c1 c2 = false is possible: need c2 < c1,
    i.e. the upper bound of i1 > the lower bound of i2. *)
Definition may_be_false_leb (h2 l1 : WithTop.with_top Z) : bool :=
  match h2, l1 with
  | WithTop.Top, _ => true
  | _, WithTop.Top => true
  | WithTop.NotTop h2', WithTop.NotTop l1' => negb (Z.leb h2' l1')
  end.

Definition interval_leb (i2 i1 : interval) : quadrivalent :=
  let (l2, h2) := i2 in
  let (l1, h1) := i1 in
  to_quadrivalent (may_be_true_leb l2 h1) (may_be_false_leb h2 l1).

Definition nbinterval_leb (i2 i1 : nb_interval) : quadrivalent := interval_leb (`i2) (`i1).

(** * Z.eqb. See [EqbTheory.v]. *)

(** Whether Z.eqb c2 c1 = true is possible: need c2 = c1,
    i.e. the intervals [l1,h1] and [l2,h2] overlap.
    Disjoint iff h1 < l2 or h2 < l1. *)
Definition may_be_true_eqb (l1 h1 l2 h2 : WithTop.with_top Z) : bool :=
  match l2, h1 with
  | WithTop.NotTop l2', WithTop.NotTop h1' => Z.leb l2' h1'
  | _, _ => true
  end &&
  match l1, h2 with
  | WithTop.NotTop l1', WithTop.NotTop h2' => Z.leb l1' h2'
  | _, _ => true
  end.

Definition may_be_false_eqb (l1 h1 l2 h2 : WithTop.with_top Z) : bool :=
  match ZInterval.is_singleton (l1, h1), ZInterval.is_singleton (l2, h2) with
  | Some x1, Some x2 => negb (Z.eqb x1 x2)
  | _, _ => true
  end. 

(** Naive [interval_eqb]: just combine [may_be_true_eqb] and
    [may_be_false_eqb] via [to_quadrivalent]. Easy to prove correct,
    but evaluates both sides even when the result is forced. A more
    efficient [interval_eqb_opt] (decision tree with shortcuts) can
    be defined separately and proved equivalent by case analysis. *)
Definition interval_eqb_unopt (i2 i1 : interval) : quadrivalent :=
  let (l2, h2) := i2 in
  let (l1, h1) := i1 in
  to_quadrivalent (may_be_true_eqb l1 h1 l2 h2) (may_be_false_eqb l1 h1 l2 h2).

Definition nbinterval_eqb_unopt (i2 i1 : nb_interval) : quadrivalent :=
  interval_eqb_unopt (`i2) (`i1).

(** Optimized [interval_eqb]: skip the [may_be_false_eqb] machinery
    (i.e. the singleton-equality test) when at least one side is not
    a singleton — in that situation [may_be_false_eqb] is always
    [true], so the result is fully determined by the overlap test. *)
Definition interval_eqb_opt (i2 i1 : interval) : quadrivalent :=
  let (l2, h2) := i2 in
  let (l1, h1) := i1 in
  match ZInterval.is_singleton (l1, h1), ZInterval.is_singleton (l2, h2) with
  | Some x1, Some x2 => if Z.eqb x1 x2 then QTrue else QFalse
  | _, _ => if may_be_true_eqb l1 h1 l2 h2 then QTop else QFalse
  end.
