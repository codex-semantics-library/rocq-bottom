(* ZIntervalBackwardOps.v - Computational backward (refinement) transfer
   functions for the ZInterval single-value abstraction. The forward ones
   are in [ZIntervalOps.v]; like them, this is the executable core,
   destined to be extracted 1:1 to OCaml, and the proofs are in the
   matching [*Theory.v] files of this directory.

   STATUS: backward add, sub (AddBackwardTheory), backward mul
   (MulBackwardTheory). *)

From Stdlib Require Import ZArith.
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

