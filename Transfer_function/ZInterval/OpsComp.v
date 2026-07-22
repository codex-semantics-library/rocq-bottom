(* OpsComp.v - Computational transfer functions for the ZInterval
   single-value abstraction. This is the executable core, destined to be
   extracted 1:1 to OCaml. Their proofs are in the matching [*Theory.v]
   files of this directory.

   STATUS: opp (OppTheory), add, sub (AddTheory), mul (MulTheory),
   quot (QuotTheory), le (LeTheory), eqb (EqbTheory). *)

From Stdlib Require Import ZArith.
Require Import
  Abstraction AbstractionCombination
  QuadrivalentTheory
  ZIntervalComp.

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
  | Across, Across =>
      (min_opt (m l1 h2) (m h1 l2), max_opt (m l1 l2) (m h1 h2))
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
  join_itv
    (interval_quot_neg_pos (fst i2, WithTop.NotTop 0) i1)
    (interval_quot_pos (WithTop.NotTop 0, snd i2) i1).

Definition interval_quot_across_neg (i2 i1 : interval) : interval :=
  join_itv
    (interval_quot_neg_neg (fst i2, WithTop.NotTop 0) i1)
    (interval_quot_pos_neg (WithTop.NotTop 0, snd i2) i1).

(** Across-divisor functions: divisor crosses zero.
    Split the divisor into [l1, -1] and [1, h1], excluding 0. *)

Definition interval_quot_pos_across (i2 i1 : interval) : interval :=
  let (l1, h1) := i1 in
  join_itv
    (interval_quot_pos_neg i2 (l1, WithTop.NotTop (-1)))
    (interval_quot_pos i2 (WithTop.NotTop 1, h1)).

Definition interval_quot_neg_across (i2 i1 : interval) : interval :=
  let (l1, h1) := i1 in
  join_itv
    (interval_quot_neg_neg i2 (l1, WithTop.NotTop (-1)))
    (interval_quot_neg_pos i2 (WithTop.NotTop 1, h1)).

(** Optimized across-divisor functions (moved here so across_across can use them). *)
Definition interval_quot_pos_across_opt (i2 i1 : interval) : interval :=
  let (_, h2) := i2 in (neg_bound h2, h2).

Definition interval_quot_neg_across_opt (i2 i1 : interval) : interval :=
  let (l2, _) := i2 in (l2, neg_bound l2).

Definition interval_quot_across_across (i2 i1 : interval) : interval :=
  let (l2, h2) := i2 in
  join_itv
    (interval_quot_neg_across_opt (l2, WithTop.NotTop 0) i1)
    (interval_quot_pos_across_opt (WithTop.NotTop 0, h2) i1).

Definition interval_quot_full (i2 i1 : interval) : interval :=
  match classify_divisor i1 with
  | DivZero => bottom
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
  match is_singleton l1 h1, is_singleton l2 h2 with
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
  match is_singleton l1 h1, is_singleton l2 h2 with
  | Some x1, Some x2 => if Z.eqb x1 x2 then QTrue else QFalse
  | _, _ => if may_be_true_eqb l1 h1 l2 h2 then QTop else QFalse
  end.
