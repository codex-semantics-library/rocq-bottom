(* ZIntervalCongruence.v - Computational core of the reduced product of
   integer intervals and integer congruences: the raw carrier, the bottom
   test, the snap helpers and the reduction. This is the executable core,
   destined to be extracted 1:1 to OCaml. Its proofs are in
   [ZIntervalCongruenceTheory.v].

   The carrier is written here as the plain pair [interval * zcongruence]
   rather than through the [Conjunction] and [CollapsedBottom] domain
   bundles, which would drag their proof fields into this file. The two
   forms are definitionally equal, so [ZIntervalCongruenceTheory.v] needs
   no bridging lemmas. *)

From Stdlib Require Import ZArith Bool.
Require Import AbstractionCombination ZInterval ZCongruence.

Open Scope Z_scope.

(** Carrier: an interval paired with a congruence, both constraining the
    same concrete value. *)
Definition zintervalcongruence := (interval * zcongruence)%type.

(** Short name, for qualified use from other modules. *)
Definition t := zintervalcongruence.

(** Canonical bottom. The interval component is γ-empty
    ([1 > 0]); the congruence component is [(0, 0)]. The conjunction
    is γ-empty regardless, so (via [CollapsedBottom]) it is [⊑] every
    element. *)
Definition bottom : zintervalcongruence :=
  (ZInterval.bottom, ZCongruence.singleton 0).

Definition is_bottomb (p : zintervalcongruence) : bool :=
  let '(i, _) := p in negb (non_bottomb i).

(** [singleton k] is the product element concretizing to exactly [{k}],
    built from the component singletons. Already reduced. *)
Definition singleton (k : Z) : zintervalcongruence :=
  (ZInterval.singleton k, ZCongruence.singleton k).

(** ** Snap helpers.

    For [m' > 0], the smallest [k ≥ lz] with [k ≡ r (mod m')] is
    [lz + (r - lz) mod m']; the largest [k ≤ hz] with [k ≡ r (mod m')]
    is [hz - (hz - r) mod m']. *)

Definition snap_low_z (lz r m' : Z) : Z := lz + (r - lz) mod m'.
Definition snap_high_z (hz r m' : Z) : Z := hz - (hz - r) mod m'.

(** ** WithTop-lifted snap. *)

Definition snap_low (l : WithTop.with_top Z) (r m' : Z) : WithTop.with_top Z :=
  match l with
  | WithTop.Top => WithTop.Top
  | WithTop.NotTop lz => WithTop.NotTop (snap_low_z lz r m')
  end.

Definition snap_high (h : WithTop.with_top Z) (r m' : Z) : WithTop.with_top Z :=
  match h with
  | WithTop.Top => WithTop.Top
  | WithTop.NotTop hz => WithTop.NotTop (snap_high_z hz r m')
  end.

(** ** Reduction.

    Given a non-bottom interval [(l, h)] and a congruence [(r, m)]:
    - if [m = 0], the cong is the singleton [{r}]; produce the
      singleton interval (or bottom if [r ∉ [l, h]]);
    - otherwise, snap each finite endpoint to the nearest element of
      [r + |m|Z], then return either bottom (if the snapped interval
      is empty), the singleton (if it collapsed to one point), or
      the snapped pair otherwise. *)

(** Build a non-empty result from snapped bounds. If both are
    [NotTop] and equal, lift the singleton into the congruence. *)
Definition build_snapped (l h : WithTop.with_top Z) (r m' : Z) : zintervalcongruence :=
  match l, h with
  | WithTop.NotTop lz, WithTop.NotTop hz =>
      if Z.ltb hz lz then bottom
      else if Z.eqb lz hz
        then singleton lz
        else ((l, h), (r, m'))
  | _, _ => ((l, h), (r, m'))
  end.

Definition reduce (p : zintervalcongruence) : zintervalcongruence :=
  let (i, c) := p in
  let (r, m) := c in
  if non_bottomb i then
    let l := fst i in
    let h := snd i in
    if Z.eqb m 0 then
      if itv_gammab (l, h) r then
        singleton r
      else bottom
    else
      let m' := Z.abs m in
      build_snapped (snap_low l r m') (snap_high h r m') r m'
  else bottom.
