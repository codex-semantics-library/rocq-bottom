(* ZIntervalAPI.v - Combines computation [ZInterval.v] and proofs
   [ZIntervalTheory.v] to an API conforming to [NONEMPTY_ABSTRACT_LATTICE]
   (checked in APICheck.v). *)

From Stdlib Require Import ZArith.
Require Import Abstraction AbstractLattice AbstractionCombination
  ZInterval ZIntervalTheory.

Open Scope Z_scope.

Definition concr : Type := Z.
Definition non_empty : Type := nb_interval.
Definition possibly_empty : Type := interval.

Definition gamma_ne (x : non_empty) : propset concr := γ[nbitv] x.
Definition gamma_pe (x : possibly_empty) : propset concr := γ[itv] x.

Definition singleton (k : concr) : non_empty :=
  exist _ (ZInterval.singleton k) (Z.le_refl k).

Definition is_included (a b : non_empty) : bool := ZInterval.is_included (`a) (`b).

Definition is_non_empty (x : possibly_empty) : bool := non_bottomb x.
Definition to_non_empty (x : possibly_empty) : option non_empty :=
  match non_bottomb x as b return non_bottomb x = b -> option non_empty with
  | true => fun H => Some (exist _ x (non_bottomb_true x H))
  | false => fun _ => None
  end (eq_refl _).

Definition singleton_sound : forall k, (k ∈ gamma_ne (singleton k)).
Proof.
  intros k. unfold gamma_ne, singleton.
  rewrite gamma_nbitv_gamma_itv. apply gamma_itv_singleton.
Qed.

Definition equiv (a b : non_empty) : bool := ZInterval.equiv (`a) (`b).
Definition join (a b : non_empty) : non_empty :=
  exist _ (ZInterval.join (`a) (`b)) (itv_join_non_bottom (`a) (`b) (proj2_sig a) (proj2_sig b)).
Definition meet (a b : non_empty) : possibly_empty := ZInterval.meet (`a) (`b).
