(* ZIntervalOps.v - Computational forward transfer functions for the
   ZInterval single-value abstraction. This is the executable core,
   destined to be extracted 1:1 to OCaml. Their proofs are in the matching
   [*Theory.v] files of this directory. The backward (refinement) transfer
   functions are in [ZIntervalBackwardOps.v].

   STATUS: opp (OppTheory), add, sub (AddTheory), mul (MulTheory),
   quot (QuotTheory), le (LeTheory), eqb (EqbTheory). *)

From Stdlib Require Import ZArith Lia.
Require Import
  Abstraction AbstractionCombination
  Primitives
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

Definition interval_sub (i1 i2 : interval) : interval :=
  let (l1,h1) := i1 in
  let (l2,h2) := i2 in
  (WithTop.lift2 Z.sub l1 h2, WithTop.lift2 Z.sub h1 l2).

(** * Z.mul. See [MulTheory.v]. *)

Definition bound_mul a b :=
  match a with
  | WithTop.NotTop x =>
    if Z.eqb x 0 then WithTop.NotTop 0
    else match b with
         | WithTop.NotTop y =>
           if Z.eqb y 0 then WithTop.NotTop 0 else WithTop.NotTop (x * y)
         | WithTop.Top => WithTop.Top
         end
  | WithTop.Top =>
    match b with
    | WithTop.NotTop y => if Z.eqb y 0 then WithTop.NotTop 0 else WithTop.Top
    | WithTop.Top => WithTop.Top
    end
  end.

Definition interval_mul (i2 i1: interval) : interval :=
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
Program Definition quot_bound (a b : WithTop.with_top Z) (Hb : b <> WithTop.NotTop 0)
  : WithTop.with_top Z :=
  match b with
  | WithTop.Top => WithTop.NotTop 0
  | WithTop.NotTop b =>
    match a with
    | WithTop.Top => WithTop.Top
    | WithTop.NotTop a => WithTop.NotTop (quot_non_zero a b _)
    end
  end.
Next Obligation. congruence. Qed.

(** The obligations [quot_bound] leaves behind are all of the form "this
    divisor bound is not [0]" — or, in the unoptimized chain of
    [QuotTheory.v], "this split half has the sign its type claims" — and
    follow from the divisor's own [proj2_sig]. The work is to expose the
    equation the [let '] pattern generalised by, and split the sigma.

    Not [Local]: [QuotTheory.v]'s chain has the same obligations and reuses
    this. *)
Ltac nz_obligation :=
  intros;
  repeat match goal with x := _ |- _ => unfold x in *; clear x end;
  repeat match goal with
         | i : pos_interval    |- _ => destruct i as [[[|?] [|?]] [? ?]]
         | i : neg_interval    |- _ => destruct i as [[[|?] [|?]] [? ?]]
         | i : across_interval |- _ => destruct i as [[[|?] [|?]] [? ?]]
         end;
  simpl in *;
  repeat match goal with
         | H : (_, _) = (_, _) |- _ => injection H; clear H; intros; subst
         end;
  repeat split;
  solve [ exact I | discriminate | contradiction | lia
        | let H := fresh in intro H; injection H; intros; subst; lia ].

#[local] Obligation Tactic := nz_obligation.

(** [i2 ÷ i1], dispatching on the sign of the divisor [i1], where
    [classify_divisor] has already removed [0] from the bounds, and then on the
    sign of the dividend [i2]. A divisor crossing zero contains ±1, so the
    quotient is bounded by [±h2] (or [±l2]) and no division happens at all.

    [Program] is here for the division-by-zero obligations, discharged by
    [nz_obligation] above. The [return interval] is not decoration: without it
    [Program] also generalises each obligation by [DivPos p = classify_divisor
    i1], pinning its type to the scrutinee, and
    [QuotTheory.interval_quot_unopt_eq] — the proof that this agrees with the
    unoptimized chain — can then no longer case on it. *)
Program Definition interval_quot (i2 : interval) (i1 : nb_interval) : interval :=
  let (l2, h2) := i2 in
  match classify_divisor i1 return interval with
  | DivZero => ZInterval.bottom
  | DivPos p =>
      let '(l1, h1) := p in
      match classify i2 with
      | Pos    => (quot_bound l2 h1 _, quot_bound h2 l1 _)
      | Neg    => (quot_bound l2 l1 _, quot_bound h2 h1 _)
      | Across => (quot_bound l2 l1 _, quot_bound h2 l1 _)
      end
  | DivNeg n =>
      let '(l1, h1) := n in
      match classify i2 with
      | Pos    => (quot_bound h2 h1 _, quot_bound l2 l1 _)
      | Neg    => (quot_bound h2 l1 _, quot_bound l2 h1 _)
      | Across => (quot_bound h2 h1 _, quot_bound l2 h1 _)
      end
  | DivAcross _ _ =>
      match classify i2 with
      | Pos    => (neg_bound h2, h2)
      | Neg    => (l2, neg_bound l2)
      | Across => ZInterval.join (l2, neg_bound l2) (neg_bound h2, h2)
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
    efficient [interval_eqb] (decision tree with shortcuts) can
    be defined separately and proved equivalent by case analysis. *)
Definition interval_eqb_unopt (i2 i1 : interval) : quadrivalent :=
  let (l2, h2) := i2 in
  let (l1, h1) := i1 in
  to_quadrivalent (may_be_true_eqb l1 h1 l2 h2) (may_be_false_eqb l1 h1 l2 h2).


(** Optimized [interval_eqb]: skip the [may_be_false_eqb] machinery
    (i.e. the singleton-equality test) when at least one side is not
    a singleton — in that situation [may_be_false_eqb] is always
    [true], so the result is fully determined by the overlap test. *)
Definition interval_eqb (i2 i1 : interval) : quadrivalent :=
  let (l2, h2) := i2 in
  let (l1, h1) := i1 in
  match ZInterval.is_singleton (l1, h1), ZInterval.is_singleton (l2, h2) with
  | Some x1, Some x2 => if Z.eqb x1 x2 then QTrue else QFalse
  | _, _ => if may_be_true_eqb l1 h1 l2 h2 then QTop else QFalse
  end.
