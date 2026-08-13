(* ZInterval.v - Computational core of the integer interval abstraction:
   the [interval] carrier, its non-bottom subset type, the lattice operations
   and the sign classifiers. This is the executable core, destined to be
   extracted 1:1 to OCaml. Its proofs are in [ZIntervalTheory.v].

   [non_bottom], [join_lb], [join_ub], [join] and the [*_gammab]
   membership tests are written here as direct matches on the bounds rather
   than as instances of the generic BoundLattice constructions, which would
   drag the [Z_CL] concrete-lattice record (and its proof fields) into this
   file. The two forms are definitionally equal, so [ZIntervalTheory.v] needs
   no bridging lemmas. *)

Require Import AbstractionCombination.
(* [Lia] discharges the sign obligations of [classify_divisor]. *)
From Stdlib Require Import Bool ZArith Lia.

Open Scope Z_scope.

Definition interval := prod (WithTop.with_top Z) (WithTop.with_top Z).

Definition non_bottom (i : interval) : Prop :=
  let (l, h) := i in
  match l with
  | WithTop.Top => True
  | WithTop.NotTop l =>
      match h with
      | WithTop.Top => True
      | WithTop.NotTop h => l <= h
      end
  end.

Definition nb_interval: Type := { i: interval | non_bottom i }.

(** A specific γ-empty interval, [(NotTop 1, NotTop 0)], representing
    the empty set of integers. Used as a result in division-by-zero. *)
Definition bottom : interval := (WithTop.NotTop 1, WithTop.NotTop 0).

Definition glbtop_is_includedb a2 a1 := 
  match a1 with
      | WithTop.Top => true
      | WithTop.NotTop a1 =>
          match a2 with
          | WithTop.Top => false
          | WithTop.NotTop a2 => Z.leb a1 a2
          end
  end.
Definition lubtop_is_includedb a2 a1 := 
  match a1 with
      | WithTop.Top => true
      | WithTop.NotTop a1 =>
          match a2 with
          | WithTop.Top => false
          | WithTop.NotTop a2 => Z.leb a2 a1
          end
  end.
Definition is_included (a2 a1: interval) := 
  let (l2,h2) := a2 in let (l1,h1) := a1 in glbtop_is_includedb l2 l1 && lubtop_is_includedb h2 h1.

Definition join_lb (a b : WithTop.with_top Z) : WithTop.with_top Z :=
  match a, b with
  | WithTop.Top, _ | _, WithTop.Top => WithTop.Top
  | WithTop.NotTop x, WithTop.NotTop y => WithTop.NotTop (Z.min x y)
  end.

Definition join_ub (a b : WithTop.with_top Z) : WithTop.with_top Z :=
  match a, b with
  | WithTop.Top, _ | _, WithTop.Top => WithTop.Top
  | WithTop.NotTop x, WithTop.NotTop y => WithTop.NotTop (Z.max x y)
  end.

Definition join (i1 i2 : interval) : interval :=
  let (l1, h1) := i1 in
  let (l2, h2) := i2 in
  (join_lb l1 l2, join_ub h1 h2).

(** Meet. Unlike the join, the meet is *exact*: [γ (meet i1 i2)] is exactly
    [γ i1 ∩ γ i2] ([itv_meet_exact]). This is what makes the calculated
    backward transfer functions optimal. It may return a γ-empty
    interval, which is intended: a backward step detecting a
    contradiction is the whole point. *)
Definition meet_lb (a b : WithTop.with_top Z) : WithTop.with_top Z :=
  match a, b with
  | WithTop.Top, x | x, WithTop.Top => x
  | WithTop.NotTop x, WithTop.NotTop y => WithTop.NotTop (Z.max x y)
  end.

Definition meet_ub (a b : WithTop.with_top Z) : WithTop.with_top Z :=
  match a, b with
  | WithTop.Top, x | x, WithTop.Top => x
  | WithTop.NotTop x, WithTop.NotTop y => WithTop.NotTop (Z.min x y)
  end.

Definition meet (i1 i2 : interval) : interval :=
  let (l1, h1) := i1 in
  let (l2, h2) := i2 in
  (meet_lb l1 l2, meet_ub h1 h2).

(** Clamping an abstract bound to a known concrete value.  These are [meet_lb b
    (NotTop k)] / [meet_ub b (NotTop k)] specialised to a known second
    argument. *)
Definition clamp_lower_bound (k : Z) (b : WithTop.with_top Z) : WithTop.with_top Z :=
  match b with
  | WithTop.Top => WithTop.NotTop k
  | WithTop.NotTop z => WithTop.NotTop (Z.max z k)
  end.

Definition clamp_upper_bound (k : Z) (b : WithTop.with_top Z) : WithTop.with_top Z :=
  match b with
  | WithTop.Top => WithTop.NotTop k
  | WithTop.NotTop z => WithTop.NotTop (Z.min z k)
  end.

(* TODO: There are more opportunitie to factor the code using these functions. *)
(** The sign halves of an interval, clamped to ∓1.  These are the
    interval-level analogues of [strictly_negative_part] /
    [strictly_positive_part] ([ZTheory.v]). *)
Definition itv_strictly_negative_part (i : interval) : interval :=
  let (l, h) := i in (l, clamp_upper_bound (-1) h).

Definition itv_strictly_positive_part (i : interval) : interval :=
  let (l, h) := i in (clamp_lower_bound 1 l, h).

(** Structural equality of intervals. Used by the backward transfer
    functions to report "nothing learned" ([None]) in the low-level
    [option]-based refinement interface; it is not a γ-level test (two
    distinct γ-empty intervals compare unequal). *)
Definition bound_equal (a b : WithTop.with_top Z) : bool :=
  match a, b with
  | WithTop.Top, WithTop.Top => true
  | WithTop.NotTop x, WithTop.NotTop y => Z.eqb x y
  | _, _ => false
  end.

Definition equiv (i1 i2 : interval) : bool :=
  let (l1, h1) := i1 in
  let (l2, h2) := i2 in
  bound_equal l1 l2 && bound_equal h1 h2.

(** Boolean form of [non_bottom], for decidability of γ-emptiness. *)
Definition non_bottomb (i : interval) : bool :=
  match i with
  | (WithTop.Top, _) => true
  | (_, WithTop.Top) => true
  | (WithTop.NotTop l, WithTop.NotTop h) => Z.leb l h
  end.

(** Join that tolerates γ-empty operands, by letting them act as identities.

    [join] itself is not a least upper bound once γ-empty intervals are ordered
    below everything: [(1,0)] is γ-empty, so [(1,0) ⊑ (2,3)], yet
    [join (1,0) (2,3) = (1,3)] is not. Guarding on [non_bottomb] repairs that,
    and this is exactly the join of the collapsed-bottom interval domain
    ([itv_canon_join_eq], [ZIntervalTheory.v]) — which is where it gets
    [JoinIsLUB], and with it the α-completeness of any sign split built on it. *)
Definition join_possibly_bottom (a b : interval) : interval :=
  if non_bottomb a then if non_bottomb b then join a b else a else b.

(** Boolean membership tests: [itv_gammab i z] decides [z ∈ γ i]. The
    bounds are annotated [Z] rather than [glb] / [lub], which are the
    [Z_CL]-derived lattices; the reflection instances are in
    [ZIntervalTheory.v]. *)
Definition glb_gammab (l : Z) z := Z.leb l z.
Definition lub_gammab (h : Z) z := Z.leb z h.

Definition itv_gammab (i:interval) z :=
  (let (l, h) := i in
   match l with
   | WithTop.Top => true
   | WithTop.NotTop l' => glb_gammab l' z
   end &&
     match h with
     | WithTop.Top => true
     | WithTop.NotTop h' => lub_gammab h' z
     end).

(** [singleton k] is the interval concretizing to exactly [{k}] — the
    constructor companion of [is_singleton]. *)
Definition singleton (k : Z) : interval := (WithTop.NotTop k, WithTop.NotTop k).

(** ** Singleton detection.

    [is_singleton i = Some x] exactly when the interval [i]
    concretizes to the single value [x]. It serves any "constant
    operand" transfer-function case; the interval×congruence product
    applies it to its interval component. *)
Definition is_singleton (i : interval) : option Z :=
  match i with
  | (WithTop.NotTop l', WithTop.NotTop h') =>
      if Z.eqb l' h' then Some l' else None
  | _ => None
  end.

Inductive classification := Pos | Neg | Across.

Definition classify (i:interval) :=
  let (l,h) := i in
  match l,h with
  | WithTop.NotTop z, _ =>
      if z >=? 0 then Pos
      else match h with
           | WithTop.NotTop z' => if z' <=? 0 then Neg else Across
           | WithTop.Top => Across
           end
  | WithTop.Top, WithTop.NotTop z =>
      if z <=? 0 then Neg else Across
  | WithTop.Top, WithTop.Top => Across
  end.

(** Sign of a bound, reading [Top] as the infinity on its own side: a
    [Top] low bound is -∞ and so never positive, a [Top] high bound is
    +∞ and so never negative. Either way [Top] is not [0], which is all
    [quot_bound] asks of it. *)
Definition low_pos  (b : WithTop.with_top Z) : Prop :=
  match b with WithTop.Top => False | WithTop.NotTop z => 0 < z end.
Definition high_pos (b : WithTop.with_top Z) : Prop :=
  match b with WithTop.Top => True  | WithTop.NotTop z => 0 < z end.
Definition low_neg  (b : WithTop.with_top Z) : Prop :=
  match b with WithTop.Top => True  | WithTop.NotTop z => z < 0 end.
Definition high_neg (b : WithTop.with_top Z) : Prop :=
  match b with WithTop.Top => False | WithTop.NotTop z => z < 0 end.

(** An interval with a definite sign. [across] needs no [non_bottom] (it is
    redundant with the bounds). All three erase to [interval]. *)
Definition pos_interval : Type := { i : interval | non_bottom i /\ low_pos (fst i) }.
Definition neg_interval : Type := { i : interval | non_bottom i /\ high_neg (snd i) }.
Definition across_interval : Type := { i : interval | low_neg (fst i) /\ high_pos (snd i) }.

(** Indexed by the interval being classified. [DivPos]/[DivNeg] carry a payload
    because they sanitize : [(NotTop 0, h)] classifies as [DivPos (NotTop 1,
    h)]; whereas [DivAcross] returns its argument untouched, so indexing lets it
    carry only the two sign facts, which are [Prop] and erase. MAYBE: separate
    sanitization and classification could be make the code cleaner. *)
Inductive divisor_classification (i : interval) : Type :=
  | DivPos : pos_interval -> divisor_classification i
  | DivNeg : neg_interval -> divisor_classification i
  | DivZero : divisor_classification i
  | DivAcross : low_neg (fst i) -> high_pos (snd i) -> divisor_classification i.

Arguments DivPos {i}. Arguments DivNeg {i}.
Arguments DivZero {i}. Arguments DivAcross {i}.

(** The same classification with the crossing case *resolved*: instead of two
    sign facts about the interval being classified, [SnapAcross] carries the two
    sign-definite halves themselves.  Dropping the index is what makes it usable
    by a domain other than [itv] — the halves no longer have to be bounds of the
    thing classified, so a domain that can name the extremal non-zero divisors
    on each side may supply those instead of the ∓1 an interval is stuck with.

    Two invariants are carried by the *choice* of constructor rather than by a
    proof, and every producer owes them: [SnapAcross n p] means both halves are
    inhabited (a divisor with nothing on one side classifies as [SnapPos] /
    [SnapNeg]), and [SnapZero] means the divisor is exactly [{0}].  That is what
    lets the crossing branch join with plain [ZInterval.join] — a hull is the
    least upper bound only when both sides are inhabited. *)
Inductive divisor_snap : Type :=
  | SnapPos : pos_interval -> divisor_snap
  | SnapNeg : neg_interval -> divisor_snap
  | SnapZero : divisor_snap
  | SnapAcross : neg_interval -> pos_interval -> divisor_snap.

(** The interval a classification actually describes: the sanitized payload in
    the sign-definite cases, and — uniformly — the hull of the two halves in the
    crossing one.  Index-free, unlike the [divisor_classification] it replaces,
    because [SnapAcross] carries the halves rather than proofs about the operand
    it came from.  γ of this is the set the snap abstracts, up to the zero
    divisors that [collecting_quot] discards anyway. *)
Definition snapped_interval (d : divisor_snap) : interval :=
  match d with
  | SnapPos p => proj1_sig p
  | SnapNeg n => proj1_sig n
  | SnapZero => bottom
  | SnapAcross n p => join (proj1_sig n) (proj1_sig p)
  end.

(** Classify the divisor, returning a sanitized interval where 0 has been
    removed from the bounds (guaranteeing that the analysis won't do a division
    by zero).

    The argument is an [nb_interval]: this allows in some cases to sanitize the
    interval by looking at a single bound. *) 
Program Definition classify_divisor (i : nb_interval)
  : divisor_classification (proj1_sig i) :=
  match proj1_sig i as x return non_bottom x -> divisor_classification x with
  | (WithTop.NotTop l', h) =>
      fun Hnb =>
      match Z_lt_dec 0 l' with
      | left Hl => DivPos (exist _ (WithTop.NotTop l', h) (conj Hnb Hl))
      | right Hl =>
        match h as hh return non_bottom (WithTop.NotTop l', hh) ->
                            divisor_classification (WithTop.NotTop l', hh) with
        | WithTop.NotTop h' =>
            fun Hnb' =>
            match Z_lt_dec h' 0 with
            | left Hh =>
                DivNeg (exist _ (WithTop.NotTop l', WithTop.NotTop h') (conj Hnb' Hh))
            | right Hh =>
              match Z.eq_dec l' 0 with
              | left _ =>
                match Z.eq_dec h' 0 with
                | left _ => DivZero
                | right Hh0 =>
                    DivPos (exist _ (WithTop.NotTop 1, WithTop.NotTop h')
                                    _)
                end
              | right Hl0 =>
                match Z.eq_dec h' 0 with
                | left _ =>
                    DivNeg (exist _ (WithTop.NotTop l', WithTop.NotTop (-1))
                                    _)
                | right Hh0 => DivAcross _ _
                end
              end
            end
        | WithTop.Top =>
            fun Hnb' =>
            match Z.eq_dec l' 0 with
            | left _ => DivPos (exist _ (WithTop.NotTop 1, WithTop.Top) _)
            | right Hl0 => DivAcross _ I
            end
        end Hnb
      end
  | (WithTop.Top, h) =>
      fun Hnb =>
      match h as hh return non_bottom (WithTop.Top, hh) ->
                          divisor_classification (WithTop.Top, hh) with
      | WithTop.NotTop h' =>
          fun Hnb' =>
          match Z_lt_dec h' 0 with
          | left Hh => DivNeg (exist _ (WithTop.Top, WithTop.NotTop h') (conj Hnb' Hh))
          | right Hh =>
            match Z.eq_dec h' 0 with
            | left _ => DivNeg (exist _ (WithTop.Top, WithTop.NotTop (-1)) _)
            | right Hh0 => DivAcross I _
            end
          end
      | WithTop.Top => fun _ => DivAcross I I
      end Hnb
  end (proj2_sig i).
Solve Obligations of classify_divisor with (simpl in *; repeat split; solve [exact I | lia]).
