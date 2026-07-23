(* OpsComp.v - Computational transfer functions for the ZIntervalCongruence
   single-value abstraction. This is the executable core, destined to be
   extracted 1:1 to OCaml. Their proofs are in the matching [*Theory.v]
   files of this directory.

   STATUS: add (AddTheory), rem (RemTheory). *)

From Stdlib Require Import ZArith Bool.
Require Import
  Abstraction AbstractLattice
  AbstractionCombination
  ZInterval
  ZCongruence ZIntervalCongruence ZIntervalCongruenceTheory
  Transfer_function.ZInterval.OpsComp
  Transfer_function.ZCongruence.OpsComp.

Open Scope Z_scope.

(** * Z.add transfer function (raw).

    [add_raw] adds the interval and congruence components independently.
    Each component operation ([interval_add], [cong_add]) is itself
    α-complete (best), so the resulting pair is already the best
    abstraction of the collecting sum — it is maximally reduced, and no
    [reduce] is needed afterwards. See [AddTheory.add],
    [AddTheory.add_raw_alpha_complete] and [AddTheory.add_alpha_complete]. *)
Definition add_raw (a2 a1 : zintervalcongruence) : zintervalcongruence :=
  let (i2, c2) := a2 in
  let (i1, c1) := a1 in
  (interval_add i2 i1, cong_add c2 c1).

(** * Z.rem. See [RemTheory.v]. *)

(** *** Adding a constant to an interval.

    [itv_add_const K i] adds [K] to both bounds of [i] ([Top] bounds stay
    [Top]). It is the abstract counterpart of [c ↦ c + K]. *)

Definition add_const_bound (K : Z) (b : WithTop.with_top Z) : WithTop.with_top Z :=
  match b with
  | WithTop.Top => WithTop.Top
  | WithTop.NotTop z => WithTop.NotTop (z + K)
  end.

Definition itv_add_const (K : Z) (i : interval) : interval :=
  (add_const_bound K (fst i), add_const_bound K (snd i)).

(** *** Constant-divisor / single-block detection.

    [const_block a2 a1 = Some (n, q)] when the divisor [a1] is a nonzero
    constant [n] ([is_singleton]) and the dividend's interval [fst a2] lies
    within a single [Z.quot _ n] block (both endpoints have quotient [q]).
    In that case [Z.rem _ n] is the affine map [c2 ↦ c2 - n*q] over
    [γ a2], whose best interval is [fst a2] shifted by [-(n*q)]. *)
Definition const_block (a2 a1 : zintervalcongruence) : option (Z * Z) :=
  match ZInterval.is_singleton (fst a1) with
  | Some n =>
      if n =? 0 then None
      else match fst a2 with
           | (WithTop.NotTop l2, WithTop.NotTop h2) =>
               if Z.quot l2 n =? Z.quot h2 n then Some (n, Z.quot l2 n) else None
           | _ => None
           end
  | None => None
  end.

(** Magnitude lower bound of a single-signed interval: [Some B] guarantees
    [0 < B <= Z.abs c] for every [c] in the interval. *)
Definition itv_abs_min (i : interval) : option Z :=
  match i with
  | (WithTop.NotTop l, WithTop.NotTop h) =>
      if 0 <? l then Some l else if h <? 0 then Some (- h) else None
  | (WithTop.NotTop l, WithTop.Top) => if 0 <? l then Some l else None
  | (WithTop.Top, WithTop.NotTop h) => if h <? 0 then Some (- h) else None
  | (WithTop.Top, WithTop.Top) => None
  end.

Definition narrow_divb (a2 a1 : zintervalcongruence) : bool :=
  match fst a2, itv_abs_min (fst a1) with
  | (WithTop.NotTop l2, WithTop.NotTop h2), Some B =>
      (Z.abs l2 <? B) && (Z.abs h2 <? B)
  | _, _ => false
  end.

Definition itv_nonnegb (i : interval) : bool :=
  match fst i with
  | WithTop.NotTop l => 0 <=? l
  | WithTop.Top => false
  end.

Definition itv_nonposb (i : interval) : bool :=
  match snd i with
  | WithTop.NotTop h => h <=? 0
  | WithTop.Top => false
  end.

Definition const_residue (a2 a1 : zintervalcongruence) : option Z :=
  match ZInterval.is_singleton (fst a1) with
  | Some n =>
      if (n =? 0) || negb (snd (snd a2) mod Z.abs n =? 0) then None
      else if itv_nonnegb (fst a2) then Some (fst (snd a2) mod Z.abs n)
      else if itv_nonposb (fst a2) then Some (- ((- fst (snd a2)) mod Z.abs n))
      else None
  | None => None
  end.

Definition rem_itv_envelope (a2 a1 : zintervalcongruence) : interval :=
  match const_block a2 a1 with
  | Some (n, q) => itv_add_const (- (n * q)) (fst a2)
  | None => if narrow_divb a2 a1 then fst a2
            else match const_residue a2 a1 with
                 | Some rho => ZInterval.singleton rho
                 | None => (WithTop.Top, WithTop.Top)
                 end
  end.

(** Divisor-trivial test for non-bottom arguments: no [is_bottomb] case
    (the argument is structurally non-empty). *)
Definition divisor_trivialb_nb (a1 : zintervalcongruence) : bool :=
  match fst a1 with
  | (WithTop.NotTop l, WithTop.NotTop h) => (l =? 0) && (h =? 0)
  | _ => false
  end.

(** Projection of a [non_bottom_zic] element to its raw [prod_ajsl]
    carrier (through the two [Subset] layers). The pattern match forces
    the [abs_car]/[ad_car] reductions a bare backtick leaves stuck. *)
Definition rd_car (a : non_bottom_zic) : zintervalcongruence :=
  match a with exist _ (exist _ a0 _) _ => a0 end.

Definition rem_cong (g2 g1 : zcongruence) : zcongruence :=
  let '(r2, m2) := g2 in
  let '(r1, m1) := g1 in
  (r2, Z.gcd m2 (Z.gcd r1 m1)).

(** Raw (unreduced) result. The interval is [rem_itv_envelope] — best on
    the constant-divisor single-block, narrow-dividend, and
    congruence-pinned-residue cases, the top interval otherwise. The
    congruence is [rem_cong] — sound on all inputs. *)
Definition rem_raw (a2 a1 : zintervalcongruence) : zintervalcongruence :=
  (rem_itv_envelope a2 a1, rem_cong (snd a2) (snd a1)).

Definition rem_final (x y : non_bottom_zic) : zic :=
  if divisor_trivialb_nb (rd_car y)
  then bottom_final
  else reduce_final (rem_raw (rd_car x) (rd_car y)).

