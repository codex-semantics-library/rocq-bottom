(* ZIntervalBackwardOps.v - Computational backward (refinement) transfer
   functions for the ZInterval single-value abstraction. The forward ones
   are in [ZIntervalOps.v]; like them, this is the executable core,
   destined to be extracted 1:1 to OCaml, and the proofs are in the
   matching [*Theory.v] files of this directory.

   STATUS: backward add, sub (AddBackwardTheory) *)

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

