(* ZTheory.v - Abstraction-independent properties of Z. *)

(** Properties of [Z] and of sets of [Z] that are not tied to any particular
    abstractions, like facts about [Z] and [℘ Z], or methods that work uniformly
    over abstractions of [Z] (like splitting at zero). *)

Require Import Abstraction.
Require Import ssreflect ssrbool ssrfun.
From Stdlib Require Import Lia. (* lia/nia; avoid Psatz which loads Reals axioms *)
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory. (* Gauss, rel_prime *)
Open Scope Z_scope.
Generalizable All Variables.

(** * Divisibility and gcd. *)

(** Cancelling a known factor against an unknown modulus: [m] divides
    [a·t] exactly when [m/gcd(m,t)] — the part of [m] that [t] does not
    already account for — divides [a].

    With [g = gcd(m,t)], [m = g·m'] and [t = g·t'], the cofactors [m']
    and [t'] are coprime, so [m' | a·t'] forces [m' | a]: that is
    [Gauss]. The other direction is immediate.  *)
Lemma Z_divide_mul_iff_div_gcd (m t a : Z) :
  t <> 0 -> ((m | a * t) <-> (m / Z.gcd m t | a)).
Proof.
  move=> Ht.
  have Hg : 0 < Z.gcd m t.
  { have Hnn := Z.gcd_nonneg m t.
    case: (Z.eq_dec (Z.gcd m t) 0) => [H0|Hne]; last lia.
    by move: (Z.gcd_eq_0_r _ _ H0). }
  have Hrp : rel_prime (m / Z.gcd m t) (t / Z.gcd m t)
    by apply/Zgcd_1_rel_prime; apply: Z.gcd_div_gcd; [lia | reflexivity].
  have Hm := Zdivide_Zdiv_eq _ _ Hg (Z.gcd_divide_l m t).
  have Htg := Zdivide_Zdiv_eq _ _ Hg (Z.gcd_divide_r m t).
  move: Hg Hrp Hm Htg. set g := Z.gcd m t. set m' := m / g. set t' := t / g.
  move=> Hg Hrp Hm Htg. rewrite Hm Htg. split.
  - move=> [k Hk]. apply: (Gauss _ t'); last exact: Hrp.
    exists k. by apply: (Z.mul_reg_l _ _ g); lia.
  - move=> [k Hk]. exists (k * t'). rewrite Hk. ring.
Qed.

(** * Sign parts of a set of integers.

    The four ways a set of integers is cut at zero.  The [strictly_] pair
    partitions a set of *non-zero* integers; the [_or_zero] pair overlaps at
    [0], which is what a total operation gets.

    We prefert the explicit "strictly" and "or_zero" to ease understanding,
    instead of the standard english nonpositive which can be confusing (as
    whether this includes zero, plus double negation).

    Written as an intersection rather than as the comprehension [{[ z | z ∈ S /\
    z < 0 ]}], because [∩] is a morphism for both [⊆⊇] and [⊆]
    ([propset_intersection_proper] / [propset_intersection_mono] in [base.v]).
    So [strictly_negative_part S] can be [rewrite]n in [S].  The comprehension
    could be rewriten if we had morphisms on [PropSet] and [propset_elem_of]
    themselves, but this would put every set comprehension in the development on
    [setoid_rewrite]'s search path.

    TODO: only this file's own lemmas use these so far.  The rest of the
    development still writes the comprehension form. Converting them is worth it
    for the same reason: it is what lets a sign half be rewritten instead of
    re-proved. *)

Definition strictly_negative_part (S : ℘ Z) : ℘ Z := S ∩ {[ z : Z | z < 0 ]}.
Definition strictly_positive_part (S : ℘ Z) : ℘ Z := S ∩ {[ z : Z | 0 < z ]}.
Definition negative_or_zero_part  (S : ℘ Z) : ℘ Z := S ∩ {[ z : Z | z <= 0 ]}.
Definition positive_or_zero_part  (S : ℘ Z) : ℘ Z := S ∩ {[ z : Z | 0 <= z ]}.
Hint Unfold strictly_negative_part strictly_positive_part
  negative_or_zero_part positive_or_zero_part : to_set.

(** * Collecting semantics.

    The primitives in [Primitives.v] are partial: each requires a non-zero
    divisor.  Their forward collecting semantics are all the same generic
    [collecting_binary_forward_partial] instance: the "divisor is non-zero"
    predicate, the one that makes [Primitives.quot_non_zero] extraction sound;
    differing only in the concrete operation [f].  [is_nonzero] names that
    shared predicate, and [collecting_non_zero_r] packages it with the
    collecting semantics; the three primitives are its instantiations. *)

Definition is_nonzero (_ c1 : Z) : Prop := c1 <> 0.

Definition collecting_non_zero_r (f : Z -> Z -> Z) (S2 S1 : propset Z) : propset Z :=
  collecting_binary_forward_partial is_nonzero f S2 S1.
Hint Unfold collecting_non_zero_r: to_set.

(** Truncating (C99) division [Z.quot]. *)
Definition collecting_quot (S2 S1 : propset Z) : propset Z :=
  collecting_non_zero_r Z.quot S2 S1.
Hint Unfold collecting_quot: to_set.

(** Floor division [Z.div]. *)
Definition collecting_div (S2 S1 : propset Z) : propset Z :=
  collecting_non_zero_r Z.div S2 S1.
Hint Unfold collecting_div: to_set.

(** Remainder of truncating division [Z.rem]. *)
Definition collecting_rem (S2 S1 : propset Z) : propset Z :=
  collecting_non_zero_r Z.rem S2 S1.
Hint Unfold collecting_rem: to_set.

(** The same guard, read backwards. [collecting_quot] above is what a *forward*
    transfer function over-approximates; these three are what the backward ones
    do, and they carry the identical [is_nonzero] guard — the divisor is still
    never [0], whichever way the arrow points.

    [_solve_left] is the dividends compatible with a divisor from [S1] and a
    quotient from [S0], with no incoming constraint on the dividend;
    [_backward_left] and [_backward_right] are that intersected with an incoming
    [S2], which is what a refinement step actually returns.  *)
Definition collecting_quot_solve_left (S1 S0 : propset Z) : propset Z :=
  collecting_binary_solve_left_partial is_nonzero Z.quot S1 S0.
Hint Unfold collecting_quot_solve_left: to_set.

Definition collecting_quot_backward_left (S2 S1 S0 : propset Z) : propset Z :=
  collecting_binary_backward_left_partial is_nonzero Z.quot S2 S1 S0.
Hint Unfold collecting_quot_backward_left: to_set.

Definition collecting_quot_backward_right (S2 S1 S0 : propset Z) : propset Z :=
  collecting_binary_backward_right_partial is_nonzero Z.quot S2 S1 S0.
Hint Unfold collecting_quot_backward_right: to_set.

(** Restricting the divisor to its nonzero elements leaves [collecting_quot]
    unchanged, so a ⊆⊇-equivalence between a divisor set and "divisors of [S1']
    distinct from 0" lifts to [collecting_quot].  Used by the dispatcher to
    relate the sanitized [DivPos] / [DivNeg] payload to the original divisor. *)
Lemma collecting_quot_restrict_equiv (S2 S1 S1' : propset Z) :
  S1 ⊆⊇ {[z | z ∈ S1' /\ z <> 0]} ->
  collecting_quot S2 S1 ⊆⊇ collecting_quot S2 S1'.
Proof.
  rewrite propset_equiv_iff => HE.
  unfold_set_equiv => z0.
  apply: exists_iff => c2; apply: exists_iff => c1.
  move: (HE c1); unfold_set; simpl. tauto.
Qed.

(** Splitting the right (divisor) operand at [< 0] / [0 <]: a strict cut that
    excludes [0].

    Hence [_split_sign] rather than [_split_zero]: the two halves partition,
    which is legitimate only under the [is_nonzero] guard. The [_split_zero_l]
    lemmas below cut at [<= 0] / [0 <=] instead, and their halves overlap at
    [0] — that is what a total operation needs. *)
Lemma collecting_non_zero_split_sign_r (f : Z -> Z -> Z) (S2 S1 : propset Z) :
  collecting_non_zero_r f S2 S1 ⊆⊇
  collecting_non_zero_r f S2 (strictly_negative_part S1) ∪
  collecting_non_zero_r f S2 (strictly_positive_part S1).
Proof.
  unfold collecting_non_zero_r.
  apply: (collecting_binary_forward_partial_split_r
            is_nonzero f S2 S1
            (strictly_negative_part S1) (strictly_positive_part S1)).
  - move=> c2 c1 Hc2 Hc1 Hne.
    unfold_set.
    case: (Z.le_gt_cases c1 0) => Hc1z; [left | right]; split=> //;
      rewrite /is_nonzero in Hne *; lia.
  - unfold_set; by move=> c [Hc _].
  - unfold_set; by move=> c [Hc _].
Qed.

(** The same cut on the *solve* side, where the divisor is the operand being
    split: what a backward transfer function needs to recover the dividend of a
    division by a divisor set that crosses zero. Same covering argument — the
    partiality has already dropped the zero divisors. *)
Lemma collecting_non_zero_solve_left_split_sign
    (f : Z -> Z -> Z) (S1 S0 : propset Z) :
  collecting_binary_solve_left_partial is_nonzero f S1 S0 ⊆⊇
  collecting_binary_solve_left_partial is_nonzero f
    (strictly_negative_part S1) S0 ∪
  collecting_binary_solve_left_partial is_nonzero f
    (strictly_positive_part S1) S0.
Proof.
  apply: (collecting_binary_solve_left_partial_split
            is_nonzero f S1
            (strictly_negative_part S1) (strictly_positive_part S1)).
  - move=> c2 c1 Hc1 Hne.
    unfold_set.
    case: (Z.le_gt_cases c1 0) => Hc1z; [left | right]; split=> //;
      rewrite /is_nonzero in Hne *; lia.
  - unfold_set; by move=> c [Hc _].
  - unfold_set; by move=> c [Hc _].
Qed.


(** * Splitting the collecting semantics at zero.

    Z-level set equivalences that cut a collecting set at [0] in the left
    operand, on arbitrary (total or partial) binary operations.  These are
    exactly [collecting_binary_forward_partial_split_l] ([Abstraction.v]) with
    the covering condition discharged against Z's total order. *)

(** Split the left operand at [<= 0] / [0 <=]. *)
Lemma collecting_binary_forward_partial_split_zero_l
  (P : Z -> Z -> Prop) (f : Z -> Z -> Z) (S2 S1 : propset Z) :
  collecting_binary_forward_partial P f S2 S1 ⊆⊇
  collecting_binary_forward_partial P f (negative_or_zero_part S2) S1 ∪
  collecting_binary_forward_partial P f (positive_or_zero_part S2) S1.
Proof.
  apply: (collecting_binary_forward_partial_split_l P f S2
            (negative_or_zero_part S2) (positive_or_zero_part S2) S1).
  - move=> c2 c1 Hc2 _ _; unfold_set.
    case: (Z.le_ge_cases c2 0) => Hc2z; [left | right]; split=> //; simpl; lia.
  - unfold_set; by move=> c [Hc _].
  - unfold_set; by move=> c [Hc _].
Qed.

(** The total (non-partial) collector [collecting_binary_forward f] splits the
    same way in its left operand. *)
Lemma collecting_binary_forward_split_zero_l
  (f : Z -> Z -> Z) (S2 S1 : propset Z) :
  collecting_binary_forward f S2 S1 ⊆⊇
  collecting_binary_forward f (negative_or_zero_part S2) S1 ∪
  collecting_binary_forward f (positive_or_zero_part S2) S1.
Proof.
  unfold_set_equiv => z; unfold_set; split.
  - move=> [c2 [c1 [Hc2 [Hc1 Heq]]]].
    case: (Z.le_ge_cases c2 0) => Hc2z; [left | right];
      exists c2, c1; (repeat split=> //); unfold_set; by split=> //; lia.
  - move=> [ [c2 [c1 [Hc2 [Hc1 Heq]]]] | [c2 [c1 [Hc2 [Hc1 Heq]]]] ];
      exists c2, c1; (repeat split=> //); by move: Hc2 => [Hc2 _].
Qed.
