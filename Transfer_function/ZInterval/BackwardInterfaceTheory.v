(* BackwardInterfaceTheory.v - The low-level refinement interface shared
   by every backward transfer function of the ZInterval abstraction.

   [impl_backward_itv] packages a left/right pair of backward transfer
   functions into the [option]-pair interface of [Abstraction.v], and its
   correctness is the same argument every time: each component is [None]
   exactly when the refinement changed nothing, and [Some i'] on a
   strictly smaller interval otherwise. The only operation-specific input
   is that each backward function does refine — it never grows its
   operand — which is what [impl_backward_itv_correct] takes as its two
   hypotheses.

   The per-operation soundness and exactness results are in the matching
   [*BackwardTheory.v] files.

   NOTE: nothing here is specific to intervals, and this file should not
   stay where it is. [impl_backward_itv] needs only a decidable equality
   on the domain the refinements live in and the projection out of the
   operand domain; [impl_backward_itv_correct] needs only that equality's
   reflection lemma and the two "this refinement shrinks" facts. Both
   belong in the framework, beside [backward_binary_function_correct], so
   that the other abstractions — and the interval × congruence product —
   share them instead of repeating this file. *)

Require Import Abstraction AbstractLattice.
Require Import ssreflect ssrbool ssrfun.
Require Import Stdlib.ZArith.ZArith.
Require Import ZInterval.
Require Import ZIntervalTheory.
Require Import Transfer_function.ZInterval.ZIntervalBackwardOps.
Open Scope Z_scope.

(** [≡] on the refined operands is structural equality. We never compare
non-bottom elements together, so we don't need to consider bottom elements as
equal. *)
Instance Equiv_interval : Equiv interval := (=).

(** The protocol [impl_backward_itv] implements is
    [backward_binary_function_correct] of [Abstraction.v] with the
    operands in [nbitv] and their refinements in [itv], embedded into
    each other by [proj1_sig]. *)
Notation backward_itv_correct :=
  (backward_binary_function_correct (R2:=itv) (R1:=itv) (A0:=nbitv)
     (@proj1_sig _ non_bottom) (@proj1_sig _ non_bottom)).

(** [refine_itv] answers [None] exactly on the intervals [itv_equalP]
    compares equal, so each component splits on that reflection: the
    [None] branch is the equality itself, and the [Some] branch is the
    refinement hypothesis together with the corresponding disequality. *)
Lemma impl_backward_itv_correct
  (bleft bright : nb_interval -> nb_interval -> nb_interval -> interval) :
  (forall i2 i1 i0, bleft  i2 i1 i0 ⊑[itv] (`i2)) ->
  (forall i2 i1 i0, bright i2 i1 i0 ⊑[itv] (`i1)) ->
  backward_itv_correct (impl_backward_itv bleft bright) bleft bright.
Proof.
  move=> Hleft Hright i2 i1 i0.
  rewrite /impl_backward_itv /refine_itv; split.
  - case: (itv_equalP (bleft i2 i1 i0) (`i2)) => [Heq|Hne] /=.
    + exact: Heq.
    + split; first done. split; [exact: Hleft | exact: Hne].
  - case: (itv_equalP (bright i2 i1 i0) (`i1)) => [Heq|Hne] /=.
    + exact: Heq.
    + split; first done. split; [exact: Hright | exact: Hne].
Qed.
