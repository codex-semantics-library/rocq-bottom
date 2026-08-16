(* ZIntervalBackwardOps.v - Computational backward (refinement) transfer
   functions for the ZInterval single-value abstraction. The forward ones
   are in [ZIntervalOps.v]; like them, this is the executable core,
   destined to be extracted 1:1 to OCaml, and the proofs are in the
   matching [*Theory.v] files of this directory.

   STATUS: backward add, sub (AddBackwardTheory), backward mul
   (MulBackwardTheory). *)

From Stdlib Require Import ZArith Lia.
Require Import
  base                       (* the [`x] notation for [proj1_sig] *)
  AbstractionCombination
  ZInterval.
Require Import Transfer_function.ZInterval.ZIntervalOps.

Open Scope Z_scope.

(** * The low-level refinement interface.

    Every backward transfer function below has the same type: it takes its three
    operands as [nb_interval] and returns a raw [interval].  Note that the
    result can be empty, since a backward step that detects a contradiction must
    be able to report a γ-empty interval.

    Both operands are refined in one call, and each result is reported as [None]
    ("nothing learned, keep the incoming interval") or [Some i'] ("refined to
    [i']"). *)

Definition refine_itv (old new : interval) : option interval :=
  if ZInterval.equiv new old then None else Some new.

Definition impl_backward_itv
  (bleft bright : nb_interval -> nb_interval -> nb_interval -> interval)
  (i2 i1 i0 : nb_interval) : option interval * option interval :=
  (refine_itv (`i2) (bleft  i2 i1 i0),
   refine_itv (`i1) (bright i2 i1 i0)).

(** Refine an operand by a *solve set* — the meet every backward transfer
    function below ends with. Note that this solve set and result can be empty,
    if there is an inconsistency. *)
Definition refine_by (i : nb_interval) (solve : interval) : interval :=
  ZInterval.meet (`i) solve.

Definition itv_top : interval := (WithTop.Top, WithTop.Top).

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

Definition backward_interval_add_left (i2 i1 i0 : nb_interval) : interval :=
  refine_by i2 (interval_sub (`i0) (`i1)).

Definition backward_interval_add_right (i2 i1 i0 : nb_interval) : interval :=
  refine_by i1 (interval_sub (`i0) (`i2)).

Definition backward_interval_sub_left (i2 i1 i0 : nb_interval) : interval :=
  refine_by i2 (interval_add (`i0) (`i1)).

Definition backward_interval_sub_right (i2 i1 i0 : nb_interval) : interval :=
  refine_by i1 (interval_sub (`i2) (`i0)).

Definition impl_backward_interval_add :=
  impl_backward_itv backward_interval_add_left backward_interval_add_right.

Definition impl_backward_interval_sub :=
  impl_backward_itv backward_interval_sub_left backward_interval_sub_right.

(** * Backward [Z.mul]. See [MulBackwardTheory.v].

    [Z.mul] is not invertible, so — unlike backward add/sub — this is only a
    sound over-approximation, neither exact nor best. The [c2 = 0] case is
    handled exactly (it admits every [c1], so nothing is learned and the operand
    is returned unchanged); the imprecision is all in the other case. It is not
    exact because divisibility is not expressible: from [2 * c1 = 1] there is no
    solution, but [[1,1] ÷ [2,2] = [0,0]] — the divisibility information that
    would tell these apart is handled by backward congruence (the interval ×
    congruence product). Some divisibility cases could be handled here (e.g. a
    constant divisor divides exactly), but we defer all of it to congruence
    rather than duplicate the machinery. Best is achievable (as a joint
    [hull(γi1 ∩ T)] over the sign regions), but the [solve]-then-[meet] shape
    here does not reach it: it loses both to divisibility and to a structural
    meet-vs-non-convex gap. See [MulBackwardTheory.v] for the two
    counterexamples. *)

(** Decides whether the solve set is all of [Z], which it is exactly when
    [0] can be both the operand and the result: [c2 = 0] then admits
    every [c1]. This branch is *exact*, not merely sound — all of
    backward mul's imprecision lives in the other one. *)
Definition mul_solve_is_top (i2 i0 : interval) : bool :=
  itv_gammab i2 0 && itv_gammab i0 0.

(** Over-approximates [{c1 | ∃ c2 ∈ γ i2, c0 ∈ γ i0, c2 * c1 = c0}].
    When the guard fails, [c2 ≠ 0] is forced, so [c1 = c0 ÷ c2] exactly
    (the division leaves no remainder) and the verified
    [interval_quot] applies. *)
Definition interval_mul_solve (i2 : nb_interval) (i0 : interval) : interval :=
  if mul_solve_is_top (`i2) i0 then itv_top
  else interval_quot i0 i2.

(** The backward mul transfer function comes in two forms. The
    [_unopt] one below is the direct transcription of the
    solve-then-meet calculation and is the one the soundness and
    precision lemmas are proved on (in [MulBackwardTheory.v]). The
    optimized one — [backward_interval_mul_right] below — exploits the
    [mul_solve_is_top] guard: when it holds, the solve set is all of
    [Z], so meeting the incoming operand with it changes nothing and
    the operand can be returned unchanged (letting the [option] layer
    report [None] for free). The two are provably equal
    ([backward_interval_mul_right_eq]), so the lemmas on the [_unopt]
    version carry over. *)
Definition backward_interval_mul_right_unopt (i2 i1 i0 : nb_interval) : interval :=
  refine_by i1 (interval_mul_solve i2 (`i0)).

(** [Z.mul] is commutative, so the left refinement is the right one with
    the operands swapped. *)
Definition backward_interval_mul_left_unopt (i2 i1 i0 : nb_interval) : interval :=
  backward_interval_mul_right_unopt i1 i2 i0.

(** The optimized right refinement: when the solve set is [⊤] the meet
    is the identity, so skip it and return the incoming operand
    unchanged. *)
Definition backward_interval_mul_right (i2 i1 i0 : nb_interval) : interval :=
  if mul_solve_is_top (`i2) (`i0) then `i1
  else refine_by i1 (interval_quot (`i0) i2).

Definition backward_interval_mul_left (i2 i1 i0 : nb_interval) : interval :=
  backward_interval_mul_right i1 i2 i0.

Definition impl_backward_interval_mul_unopt :=
  impl_backward_itv backward_interval_mul_left_unopt backward_interval_mul_right_unopt.

(** The fully optimized interface. Bypasses [refine_by] (and thus the
    [meet]) entirely: each component returns [None] directly when its
    [mul_solve_is_top] guard fires (the solve set is [⊤], so the meet is
    the identity), and [refine_itv] of the meet with the quotient
    otherwise. The two components carry independent guards, since
    [Z.mul] is commutative and the left refinement is the right one on
    the swapped operands. Provably equal to
    [impl_backward_interval_mul_unopt]
    ([impl_backward_interval_mul_eq] in [MulBackwardTheory.v]), so the
    soundness and correctness lemmas carry over. *)
Definition backward_mul_refine
  (iR i0 iKeep : nb_interval) : option interval :=
  if mul_solve_is_top (`iR) (`i0) then None
  else refine_itv (`iKeep) (ZInterval.meet (`iKeep) (interval_quot (`i0) iR)).

Definition impl_backward_interval_mul
  (i2 i1 i0 : nb_interval) : option interval * option interval :=
  (backward_mul_refine i1 i0 i2, backward_mul_refine i2 i0 i1).

(** * Backward [Z.quot]. See [QuotBackwardTheory.v]. *)


(** ** Refining the dividend. *)

(** Bounds the remainder [Z.rem c2 c1] of the division being inverted by
    the largest magnitude a divisor drawn from [i1] can have. The bound
    is [Z.max (Z.abs l) (Z.abs h) - 1] when both bounds of [i1] are
    finite, and [⊤] otherwise — the interval is unbounded, so the
    remainder is too. The result is the symmetric interval [[-b, b]]. *)
Definition quot_remainder_window_sym (i1 : interval) : interval :=
  match i1 with
  | (WithTop.NotTop l, WithTop.NotTop h) =>
      let m := Z.max (Z.abs l) (Z.abs h) - 1 in
      (WithTop.NotTop (- m), WithTop.NotTop m)
  | _ => itv_top
  end.

(** The remainder carries the sign of the dividend, and when the
    quotient is non-zero the dividend carries the sign of [c0 * c1]
    (the remainder is too small to pull it across zero). So whenever
    [0 ∉ γ i0] and the product has a definite sign, the window is
    one-sided: [c2] lies strictly *away* from zero relative to
    [c0 * c1], never on the near side. This is what makes
    [x ÷ 3 = 5] give the exact [[15,17]] rather than [[13,17]].

    The clamp is worth applying even when [quot_remainder_window_sym] is [⊤]: an
    unbounded divisor still leaves the *sign* of the remainder known.

    [p] is the product [i0 * i1], taken as an argument because the
    caller has already computed it. *)
Definition quot_remainder_window (p i1 i0 : interval) : interval :=
  let s := quot_remainder_window_sym i1 in
  if itv_gammab i0 0 then s
  else match classify p with
       | Pos    => (WithTop.NotTop 0, snd s)
       | Neg    => (fst s, WithTop.NotTop 0)
       | Across => s
       end.

Definition interval_quot_solve_dividend (i1 i0 : interval) : interval :=
  let p := interval_mul i0 i1 in
  interval_add p (quot_remainder_window p i1 i0).

(** The divisor of a division being inverted is never [0], so only its sign
    halves matter — and taking them serves both of the things a raw
    [interval_quot_solve_dividend] gets wrong.

    A divisor *crossing* zero must be split: the largest product wants the
    divisor of one sign and the largest remainder the other, so no single
    application realises both and the answer is genuinely too wide —
    [i1 = [-3,2]], [i0 = [1,100]] gives [[-302,202]] where the hull of the
    solve set is [[-302,201]]. Splitting and joining is exact, for arbitrary
    operand sets ([interval_quot_solve_dividend_split_across_alpha_complete]).

    A divisor with [0] on a *bound* needs no split — [classify] already calls
    it [Pos] or [Neg] — but does need that bound moved off zero, which is the
    same clamp applied on one side only: [[0,h]] becomes [[1,h]]. That
    recovers bestness there ([interval_quot_solve_dividend_split_best]), though not
    α-completeness, because the clamp claims a divisor ∓1 that an arbitrary
    operand set need not contain.

    The sign halves are [itv_strictly_negative_part] /
    [itv_strictly_positive_part] from the carrier ([ZInterval.v]): the ∓1
    clamp is exactly the interval-specific weakening — an interval can only
    claim the extremal nonzero divisor ∓1, never the actual nearest divisor.
    The congruence product's [divisor_{neg,pos}_half]
    ([ZIntervalCongruenceOps.v]) is the same operation wrapped in [reduce],
    which snaps the inner bound to the extremal divisor that is really
    there.

    Nothing computes with this: the backward dividend below always solves
    against an already-clamped half, so it calls the unsplit form
    ([interval_quot_dividend_from_divisor_half]). The definition stays
    because it is what the bestness and α-completeness statements just
    described are about. *)
Definition interval_quot_solve_dividend_split (i1 i0 : interval) : interval :=
  match classify i1 with
  | Pos    => interval_quot_solve_dividend (ZInterval.itv_strictly_positive_part i1) i0
  | Neg    => interval_quot_solve_dividend (ZInterval.itv_strictly_negative_part i1) i0
  | Across => ZInterval.join
                 (interval_quot_solve_dividend (ZInterval.itv_strictly_negative_part i1) i0)
                 (interval_quot_solve_dividend (ZInterval.itv_strictly_positive_part i1) i0)
  end.

(** The dividend's refinement is *not* [refine_by i2] of the solve set above,
    and cannot be: the solve set is a union of blocks with gaps between them
    ([i1 = [2,3]], [i0 = [5,5]] gives [[10,11] ∪ [15,17]]), so meeting its hull
    with [i2] lets the gaps back in — [i2 = [12,16]] would give [[12,16]] where
    [[15,16]] is right. It is defined after the divisor, below, because the
    repair uses the divisor's own refinement. *)

(** ** Refining the divisor.

    Unlike the dividend, this side is exact, and the reason is that the
    divisor's solve set has no holes once its sign is fixed. For [b ≥ 1],

<<
      b is compatible  <->  some c2 ∈ γ i2 has  c2 ÷ b ∈ γ i0
                       <->  m(b) ≤ h2  /\  l2 ≤ M(b)
>>

    where [m(b)] and [M(b)] are the least and greatest dividend whose
    quotient by [b] stays within [γ i0] — that is, the two ends of
    [interval_quot_solve_dividend (b,b) i0], the dividend refinement of the
    previous section applied to a single divisor. Both are *affine* in
    [b], so each of the two conditions holds on a half-line and the
    compatible divisors form an interval. That is what the dividend side
    lacks: there the solve set is a union of blocks with gaps between
    them ([[10,11] ∪ [15,17]]), so meeting it with the incoming interval
    loses; here nothing is lost, provided the meet is taken *inside each
    sign half* — hence [interval_quot_solve_divisor_split] below takes the
    incoming divisor as an argument rather than meeting afterwards.

    Solving those two conditions for [b] is a division — the *same*
    division, so this section computes with [quot_bound], the forward
    transfer function's own bound operator ([ZIntervalOps.v]), and not with
    [Z.div]. Three things fall out of that choice:

    - the ∞ conventions are the forward ones and they are exactly right
      here. [quot_bound Top b = Top] says an unbounded dividend leaves the
      constraint vacuous, at either end; [quot_bound a Top = 0] turns an
      unbounded *quotient* bound into the vacuous divisor bound [b ≥ 1]
      after the [+1] below;
    - truncation rather than flooring costs nothing. The exact solutions are
      a floor and a ceiling, and they differ from the truncated forms only
      where the answer is below [1] — where the clamp to [b ≥ 1] erases the
      difference (checked exhaustively over [[-8,8]]);
    - it keeps the domain on one division primitive. Extraction realizes
      [quot_non_zero] only ([ocaml/extraction/PrimitiveExtraction.v]);
      [Z.div] is deliberately left unrealized, so a floor here would be an
      unrealized primitive the day this function is extracted. *)

(** Successor of a bound, an infinity being its own successor. *)
Definition bound_succ (b : WithTop.with_top Z) : WithTop.with_top Z :=
  match b with
  | WithTop.Top => WithTop.Top
  | WithTop.NotTop z => WithTop.NotTop (z + 1)
  end.

(** Predecessor, the same way. The negative divisor half below turns every
    [+1] of the positive one into this, since it bounds the divisor from the
    other side. *)
Definition bound_pred (b : WithTop.with_top Z) : WithTop.with_top Z :=
  match b with
  | WithTop.Top => WithTop.Top
  | WithTop.NotTop z => WithTop.NotTop (z - 1)
  end.

(** [quot_bound] at a finite, non-zero divisor bound. Every division below
    divides by a *shifted* bound of the quotient interval — shifted precisely
    because the unshifted one may be [0] — so the sign test that chooses the
    branch also supplies this argument, and no [Program] obligation arises. *)
Definition quot_bound_nz (a : WithTop.with_top Z) (z : Z) (H : z <> 0)
  : WithTop.with_top Z :=
  quot_bound a (WithTop.NotTop z) ltac:(congruence).

(** The constraint the *low* end of the quotient puts on a positive divisor
    [b]: some dividend at most [h2] must reach a quotient of at least [l0],
    i.e. [m(b) ≤ h2] with [m(b) = l0*b - (b-1)*[l0 ≤ 0]].

    The sign of [l0] decides which way it points, and this is the antitony of
    division: a *positive* quotient bound caps the divisor ([l0*b ≤ h2], so
    [b ≤ h2 ÷ l0]), a non-positive one puts a floor under it
    ([(l0-1)*b + 1 ≤ h2], so [b ≥ h2 ÷ (l0-1) + 1], the divisor of that
    division being negative). Both are one [quot_bound] call. *)
Definition quot_divisor_pos_qlow (h2 l0 : WithTop.with_top Z) : interval :=
  match l0 with
  | WithTop.Top => itv_top
  | WithTop.NotTop z =>
      match Z_lt_le_dec 0 z with
      | left H  => (WithTop.Top, quot_bound_nz h2 z ltac:(lia))
      | right H => (bound_succ (quot_bound_nz h2 (z - 1) ltac:(lia)), WithTop.Top)
      end
  end.

(** The mirror constraint from the *high* end of the quotient: some dividend
    at least [l2] must stay under a quotient of [h0], i.e. [l2 ≤ M(b)] with
    [M(b) = h0*b + (b-1)*[0 ≤ h0]]. The sign of [h0] decides, the other way
    round.

    Note what a quotient containing [0] does: both constraints are then
    floors and the divisor is left unbounded above, which is right — any
    large enough divisor quotients to [0]. It is also the case the old
    magnitude bound gave up on entirely, returning ⊤. *)
Definition quot_divisor_pos_qhigh (l2 h0 : WithTop.with_top Z) : interval :=
  match h0 with
  | WithTop.Top => itv_top
  | WithTop.NotTop z =>
      match Z_lt_le_dec z 0 with
      | left H  => (WithTop.Top, quot_bound_nz l2 z ltac:(lia))
      | right H => (bound_succ (quot_bound_nz l2 (z + 1) ltac:(lia)), WithTop.Top)
      end
  end.

(** The positive divisors compatible with a dividend in [i2] and a quotient
    in [i0]: the two constraints above, and [1 ≤ b]. May be γ-empty, which
    is the transfer function reporting a contradiction. The [1 ≤ b] clamp
    is [itv_strictly_positive_part] applied to the two-constraint meet. *)
Definition interval_quot_solve_divisor_pos (i2 i0 : interval) : interval :=
  ZInterval.itv_strictly_positive_part
    (ZInterval.meet (quot_divisor_pos_qlow (snd i2) (fst i0))
                    (quot_divisor_pos_qhigh (fst i2) (snd i0))).

(** The negative divisors, by [c2 ÷ (-b) = -(c2 ÷ b)]: negate the quotient
    interval, solve for a positive divisor, negate back.

    This is the specification. The version that gets extracted is the one
    below, with the round trip pushed through the computation. *)
Definition interval_quot_solve_divisor_neg_unopt (i2 i0 : interval) : interval :=
  interval_opp (interval_quot_solve_divisor_pos i2 (interval_opp i0)).

(** The same solve set, computed directly. [interval_opp] distributes over
    [ZInterval.meet] and exchanges the two sign halves, and [Z.quot_opp_r]
    absorbs the surviving negation into each division, so nothing is left of
    the round trip but a mirror of the two constraints above — with the sign
    tests pointing the other way and the shifts going the other way.

    Which bounds each constraint reads is the antitony of division again, and
    it is what the negation of [i0] amounts to: dividing by a *negative* [b]
    is decreasing in the dividend, so the largest dividend is the one that
    reaches the smallest quotient. The high end of the quotient is therefore
    constrained by the high end of the dividend — [h2 ÷ b ≤ h0] — where the
    positive half paired [h2] with [l0]. Same two divisions, no
    [interval_opp]; provably equal to [_unopt]
    ([interval_quot_solve_divisor_neg_eq], [QuotBackwardTheory.v]), so the
    lemmas proved on that one carry over. *)
Definition quot_divisor_neg_qhigh (h2 h0 : WithTop.with_top Z) : interval :=
  match h0 with
  | WithTop.Top => itv_top
  | WithTop.NotTop z =>
      match Z_lt_le_dec z 0 with
      | left H  => (quot_bound_nz h2 z ltac:(lia), WithTop.Top)
      | right H => (WithTop.Top, bound_pred (quot_bound_nz h2 (z + 1) ltac:(lia)))
      end
  end.

Definition quot_divisor_neg_qlow (l2 l0 : WithTop.with_top Z) : interval :=
  match l0 with
  | WithTop.Top => itv_top
  | WithTop.NotTop z =>
      match Z_lt_le_dec 0 z with
      | left H  => (quot_bound_nz l2 z ltac:(lia), WithTop.Top)
      | right H => (WithTop.Top, bound_pred (quot_bound_nz l2 (z - 1) ltac:(lia)))
      end
  end.

Definition interval_quot_solve_divisor_neg (i2 i0 : interval) : interval :=
  ZInterval.itv_strictly_negative_part
    (ZInterval.meet (quot_divisor_neg_qhigh (snd i2) (snd i0))
                    (quot_divisor_neg_qlow  (fst i2) (fst i0))).

(** The divisor refinement: solve within each sign half, meet with the
    incoming divisor *there*, and join. The meet has to happen before the
    join — meeting afterwards would let the hull's inner points back in, and
    that alone loses on 99 007 of the 753 571 boxes over [[-6,6]] (see
    [todo/quot_backward_divisor.md]).

    No [classify] dispatch: a half that cannot occur comes out γ-empty and
    [join_possibly_bottom] drops it. That also subsumes the old
    [itv_remove_zero] — the two halves are clamped off zero by construction,
    so a [0] sitting on a bound of the incoming divisor is removed with no
    extra machinery.

    [ZInterval.join] takes the componentwise min and max, which is the hull
    only when both sides are inhabited — a γ-empty side would contribute its
    stray bounds. On the dividend side that never arises; here it does, since
    a sign half can be ruled out entirely ([100 ÷ y = 3] admits no negative
    [y]), so the join has to check. *)
Definition interval_quot_solve_divisor_split_unopt (i2 i1 i0 : interval) : interval :=
  ZInterval.join_possibly_bottom
    (ZInterval.meet (ZInterval.itv_strictly_negative_part i1) (interval_quot_solve_divisor_neg i2 i0))
    (ZInterval.meet (ZInterval.itv_strictly_positive_part i1) (interval_quot_solve_divisor_pos i2 i0)).

(** The same thing without the two clamps on [i1], which is what gets
    extracted. Each solve half is *already* clamped off zero — that is the
    trailing [itv_strictly_{positive,negative}_part] of
    [interval_quot_solve_divisor_{pos,neg}] — and [meet_lb] is a [Z.max], so
    clamping [i1] as well contributes nothing
    ([itv_meet_strictly_positive_part_absorb], [ZIntervalTheory.v]). The two
    are equal ([interval_quot_solve_divisor_split_eq]), so the lemmas above
    keep their shape; [_unopt] is what they are proved on.

    Keeping [_unopt] is not just bookkeeping. Those two meets are where a
    divisor half with a bound *better* than ∓1 belongs — the congruence
    product's [divisor_{neg,pos}_half] ([ZIntervalCongruenceOps.v]), which
    snaps the inner bound to the extremal divisor that is really there. The
    clamp is redundant only because an interval can claim nothing sharper
    than ∓1; a snapped half is not, and would go back exactly here.

    It also dispatches on [classify i1], which [_unopt] deliberately does not.
    That dispatch buys nothing in precision — it is emptiness of a half that
    rules the wrong sign out, and [join_possibly_bottom] already drops an
    empty half — but it lets the *computation* of that half be skipped, and
    the half costs two divisions. A divisor with [l1 ≥ 0] cannot be negative,
    so the negative half's meet is γ-empty whatever it contains; likewise
    [h1 ≤ 0] and the positive half. Only a strictly straddling divisor needs
    both, and then the join is still the guarded one, since a sign half can
    be ruled out by the *dividend* rather than by [i1].

    Equal to [_unopt] at γ, not on the nose
    ([interval_quot_solve_divisor_split_gamma_eq]): when the divisor is
    contradicted outright, both halves are γ-empty and the left-biased
    [join_possibly_bottom] returns the positive half's stray bounds where the
    [Neg] branch here returns the negative half's. Both are ⊥, and γ is all
    that [Overapproximates] and [MostPrecise] read. *)
Definition interval_quot_solve_divisor_split (i2 i1 i0 : interval) : interval :=
  match classify i1 with
  | Pos    => ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0)
  | Neg    => ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0)
  | Across => ZInterval.join_possibly_bottom
                (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0))
                (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0))
  end.

Definition backward_interval_quot_divisor (i2 i1 i0 : nb_interval) : interval :=
  interval_quot_solve_divisor_split (`i2) (`i1) (`i0).

(** ** Refining the dividend, after the divisor.

    A block [W(c1)] — the dividends that a *fixed* divisor [c1] sends into
    [γ i0] — is an interval with no holes ([quot_window_iff]). The solve set is
    their union over [c1], and meeting a union of intervals with [i2] loses
    exactly one thing: blocks that miss [γ i2] entirely still contribute their
    ends to the hull. Drop those blocks and nothing is lost —

<<
      hull(A ∩ ⋃ B_k) = A ∩ hull(⋃ B_k)   when every B_k meets A
>>

    — and the divisors whose block meets [γ i2] are precisely what the previous
    section computes. So the repair is not a sharper solve set (that one is
    already exact) but a smaller *divisor*: refine it first, then solve the
    dividend against the refined one.

    Done per sign half, because that is where the divisor's refinement is
    exactly the feasible set rather than its hull. The guard is not
    decoration: on a γ-empty half [interval_quot_solve_dividend] can return a
    *non-empty* interval, so the half has to be dropped explicitly.

    The meet with [i2] stays *outside* the guard, which makes this the same
    "meet the operand with a solve set" every other backward function here is
    ([refine_by], above) — the guard only chooses *which* solve set, the half's
    or ⊥.

    It has to stay outside. [⊑[itv]] is the componentwise order on the two
    bounds ([is_includedP], [ZIntervalTheory.v]), so it never notices that an
    interval is γ-empty: against [i2 = [5,10]] the constant [ZInterval.bottom]
    = [[1,0]] fails [⊑], because its low bound [1] *forgets* [x ≥ 5]. (Against
    [i2 = [-3,4]] it passes — which is worse than failing outright, since the
    obligation then holds by accident of where [i2] sits.) [meet i2 ⊥] takes
    the stronger of each bound, so it is [⊑ i2] by construction
    ([itv_meet_lower_bound_l]) and still γ-empty. That is what
    [backward_interval_quot_dividend_lower_bound] rests on, and through it the
    [option] protocol's "a refinement never grows its operand".

    Nothing downstream repairs a raw ⊥ for us: [join_possibly_bottom] hands
    back an operand *verbatim* when the other is γ-empty, so it would escape to
    [refine_itv], which reports it as-is. [refine_itv] could be taught to clamp
    it, but then every backward function pays that test, and
    [impl_backward_itv_correct]'s hypothesis — stated on the refinement
    function itself — would have to weaken to "γ-empty or [⊑]".

    The [classify] dispatch is the divisor's, for the same reason and with the
    same payoff: a half that cannot occur is γ-empty, so it may as well not be
    computed, and a half costs two divisions. Both components branch the same
    way, which is what lets the shared form below be an equality on the nose.

    The solve step is the *unsplit* [interval_quot_solve_dividend], not
    [interval_quot_solve_dividend_split]. Every [F] reaching here is a solved
    half — [meet i1 (interval_quot_solve_divisor_{pos,neg} i2 i0)] — whose
    inner bound the divisor solver's trailing
    [itv_strictly_{positive,negative}_part] has already moved off zero, so the
    [classify] dispatch and the ∓1 clamp inside [_split] would both be no-ops.
    [interval_quot_solve_dividend_split_{pos,neg}_preclamped]
    ([QuotBackwardTheory.v]) say exactly that, and are what the bestness proofs
    of the two halves go through. *)
Definition interval_quot_dividend_from_divisor_half
    (i2 F i0 : interval) : interval :=
  ZInterval.meet i2
    (if ZInterval.non_bottomb F
     then interval_quot_solve_dividend F i0
     else ZInterval.bottom).

Definition interval_quot_dividend_refine (i2 i1 i0 : interval) : interval :=
  match classify i1 with
  | Pos => interval_quot_dividend_from_divisor_half i2
             (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0)) i0
  | Neg => interval_quot_dividend_from_divisor_half i2
             (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0)) i0
  | Across =>
      ZInterval.join_possibly_bottom
        (interval_quot_dividend_from_divisor_half i2
           (ZInterval.meet i1 (interval_quot_solve_divisor_neg i2 i0)) i0)
        (interval_quot_dividend_from_divisor_half i2
           (ZInterval.meet i1 (interval_quot_solve_divisor_pos i2 i0)) i0)
  end.

Definition backward_interval_quot_dividend (i2 i1 i0 : nb_interval) : interval :=
  interval_quot_dividend_refine (`i2) (`i1) (`i0).

(** The composed interface: each refinement computed independently, which is
    what the [option] protocol is stated on. *)
Definition impl_backward_interval_quot_unopt :=
  impl_backward_itv backward_interval_quot_dividend backward_interval_quot_divisor.

(** The extracted one, which computes the two sign halves **once** and builds
    both refinements from them. This is the whole reason the dividend's repair
    is free: it needs exactly the halves the divisor's refinement already is,
    so sharing them leaves the division count where the divisor alone put it —
    two on a sign-definite divisor, four on a straddling one — instead of
    doubling it.

    Equal to [_unopt] on the nose ([impl_backward_interval_quot_eq]), because
    both components branch on the same [classify] and each branch is the same
    pair of expressions with the halves named. *)
Definition impl_backward_interval_quot (i2 i1 i0 : nb_interval)
  : option interval * option interval :=
  match classify (`i1) with
  | Pos =>
      let Fp := ZInterval.meet (`i1) (interval_quot_solve_divisor_pos (`i2) (`i0)) in
      (refine_itv (`i2) (interval_quot_dividend_from_divisor_half (`i2) Fp (`i0)),
       refine_itv (`i1) Fp)
  | Neg =>
      let Fn := ZInterval.meet (`i1) (interval_quot_solve_divisor_neg (`i2) (`i0)) in
      (refine_itv (`i2) (interval_quot_dividend_from_divisor_half (`i2) Fn (`i0)),
       refine_itv (`i1) Fn)
  | Across =>
      let Fn := ZInterval.meet (`i1) (interval_quot_solve_divisor_neg (`i2) (`i0)) in
      let Fp := ZInterval.meet (`i1) (interval_quot_solve_divisor_pos (`i2) (`i0)) in
      (refine_itv (`i2) (ZInterval.join_possibly_bottom
                           (interval_quot_dividend_from_divisor_half (`i2) Fn (`i0))
                           (interval_quot_dividend_from_divisor_half (`i2) Fp (`i0))),
       refine_itv (`i1) (ZInterval.join_possibly_bottom Fn Fp))
  end.

(** * Backward [Z.lxor]. See [LxorBackwardTheory.v].

    [Z.lxor] is its own inverse in each argument — [c2 ^ c1 = c0 <-> c0 ^ c1 =
    c2] — so, as for [Z.add] and [Z.sub], the solve set *is* a forward image
    and the transfer function is "meet with the forward image of the inverse".
    The inverse being [Z.lxor] itself, the solve step needs no new arithmetic
    whatever: [interval_lxor] is already the best abstraction of that image
    ([interval_lxor_best]), so the solve step is best as it stands.

    Unlike add and sub this is not exact, and the reason is not in the solve
    step. The image of [Z.lxor] over two intervals has holes — [{1} ^ [0,2] =
    {0,1,3}] — so the best interval is strictly wider than the solve set, and
    the meet lets the hull-only points back in. That is the same structural
    gap backward mul has, and it is the only one here: no [Z.lxor] analogue of
    mul's divisibility loss exists. See [backward_interval_lxor_not_best].

    [Z.land] and [Z.lor] get nothing from this: neither is invertible, and
    their solve sets are not forward images of anything already defined. *)

Definition backward_interval_lxor_left (i2 i1 i0 : nb_interval) : interval :=
  refine_by i2 (interval_lxor (`i0) (`i1)).

(** [Z.lxor] is commutative, so the right refinement is the left one with
    the operands swapped. *)
Definition backward_interval_lxor_right (i2 i1 i0 : nb_interval) : interval :=
  backward_interval_lxor_left i1 i2 i0.

Definition impl_backward_interval_lxor :=
  impl_backward_itv backward_interval_lxor_left backward_interval_lxor_right.
