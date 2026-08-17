(** Backward.v - The low-level interface of backward (refinement) transfer
   functions: its result type and the packaging that builds one. This is the
   executable core; the specification it satisfies and the correctness of the
   packaging are in [BackwardTheory.v].

   A backward step asks what values of an operand could have produced a given
   result against the other operand. Its answer has three shapes, and the
   first is the one a plain [option] per operand cannot express:

   - the constraint is *unsatisfiable*, so no value of *either* operand
     survives. This is a property of the whole step rather than of one
     operand: the two refinements are the two projections of a single
     relation, and a projection is empty exactly when the relation is
     ([collecting_binary_backward_empty_iff], [Abstraction.v]). So it is
     hoisted out of the pair, as [WithBottom.Bot];
   - an operand is *unchanged* — nothing was learned, [None];
   - an operand is *refined*, [Some a'] with [a'] strictly below it.

   Note that NotTop does not mean that the element must concretize to a
   non-empty set, only that unsatisfiability was not detected.

   It is also *more precise* than reporting per-operand emptiness, on any
   operation whose two sides are not both optimal: when one side detects a
   contradiction and the other does not, the hoisted form keeps the detection
   and discards the other side's unreliable non-empty answer. *)

Require Import AbstractionCombination.   (* [WithBottom.with_bottom] *)

(** * The two result types. *)

Definition unary_result (A1 : Type) : Type :=
  WithBottom.with_bottom (option A1).

Definition binary_result (A2 A1 : Type) : Type :=
  WithBottom.with_bottom (option A2 * option A1)%type.

(** * Packaging a raw refinement into the interface.

    [to_non_empty] is the domain's partial "view this as non-empty"
    constructor ([ZIntervalAPI.to_non_empty] is one, [Quadrivalent.to_non_bottom]
    the other), [proj] the projection back out to the wide domain the raw
    refinement lives in, and [eqb] a decidable equality there — used only to
    answer "did anything change?". *)

Section Unary.
  Context {R A : Type}.
  Variable to_non_empty : R -> option A.
  Variable proj : A -> R.
  Variable eqb : R -> R -> bool.

  (** What to report for an operand [a] whose refinement computed to [r],
      seen as the non-empty [b]: [None] exactly when [r] left [a] where it
      was. *)
  Definition refinement (a : A) (r : R) (b : A) : option A :=
    if eqb r (proj a) then None else Some b.

  Definition hoist_unary (a : A) (r : R) : unary_result A :=
    match to_non_empty r with
    | Some b => WithBottom.NotBot (refinement a r b)
    | None => WithBottom.Bot
    end.
End Unary.

Section Binary.
  Context {R2 A2 R1 A1 : Type}.
  Variables (to_non_empty2 : R2 -> option A2) (proj2 : A2 -> R2)
            (eqb2 : R2 -> R2 -> bool).
  Variables (to_non_empty1 : R1 -> option A1) (proj1 : A1 -> R1)
            (eqb1 : R1 -> R1 -> bool).

  Definition hoist_binary (a2 : A2) (a1 : A1) (r2 : R2) (r1 : R1)
    : binary_result A2 A1 :=
    match to_non_empty2 r2, to_non_empty1 r1 with
    | Some b2, Some b1 =>
        WithBottom.NotBot
          (refinement proj2 eqb2 a2 r2 b2, refinement proj1 eqb1 a1 r1 b1)
    | _, _ => WithBottom.Bot
    end.
End Binary.
