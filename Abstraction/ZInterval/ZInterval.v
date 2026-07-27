(* ZInterval.v - Computational core of the integer interval abstraction:
   the [interval] carrier, its non-bottom subset type, the lattice operations
   and the sign classifiers. This is the executable core, destined to be
   extracted 1:1 to OCaml. Its proofs are in [ZIntervalTheory.v].

   [non_bottom], [join_lb], [join_ub], [itv_join] and the [*_gammab]
   membership tests are written here as direct matches on the bounds rather
   than as instances of the generic BoundLattice constructions, which would
   drag the [Z_CL] concrete-lattice record (and its proof fields) into this
   file. The two forms are definitionally equal, so [ZIntervalTheory.v] needs
   no bridging lemmas. *)

Require Import AbstractionCombination.
From Stdlib Require Import Bool ZArith.

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
Definition itv_is_includedb (a2 a1: interval) := 
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

Definition itv_join (i1 i2 : interval) : interval :=
  let (l1, h1) := i1 in
  let (l2, h2) := i2 in
  (join_lb l1 l2, join_ub h1 h2).

(** Meet. Unlike the join, the meet is *exact*: [γ (itv_meet i1 i2)] is exactly
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

Definition itv_meet (i1 i2 : interval) : interval :=
  let (l1, h1) := i1 in
  let (l2, h2) := i2 in
  (meet_lb l1 l2, meet_ub h1 h2).

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

Definition itv_equal (i1 i2 : interval) : bool :=
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

(** Classify the divisor, and returns an interval where 0 has been
removed from the bounds. *)
Inductive divisor_classification :=
  | DivPos : interval -> divisor_classification
  | DivNeg : interval -> divisor_classification
  | DivZero
  | DivAcross.

Definition classify_divisor (i:interval) :=
  let (l,h) := i in
  match l with
  | WithTop.NotTop l' =>
      if l' >? 0 then DivPos i
      else match h with
           | WithTop.NotTop h' =>
               if h' <? 0 then DivNeg i
               else if Z.eqb l' 0 then
                      if  Z.eqb h' 0 then DivZero
                      else DivPos (WithTop.NotTop 1, h)
                    else if Z.eqb h' 0 then DivNeg (l, WithTop.NotTop (-1))
               else DivAcross
           | WithTop.Top =>
               if Z.eqb l' 0
               then DivPos (WithTop.NotTop 1, h)
               else DivAcross
           end
  | WithTop.Top =>
      match h with
       | WithTop.NotTop h' =>
           if h' <? 0 then DivNeg i
           else if Z.eqb h' 0 then DivNeg (l, WithTop.NotTop (-1))
           else DivAcross
       | WithTop.Top => DivAcross
      end
  end.
