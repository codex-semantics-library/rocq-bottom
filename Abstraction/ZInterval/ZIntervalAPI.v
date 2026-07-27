(* ZIntervalAPI.v - Combines computation [ZInterval.v] and proofs
   [ZIntervalTheory.v] to an API conforming to [NONEMPTY_ABSTRACT_LATTICE]
   (checked in APICheck.v). *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ssreflect ssrbool ssrfun.
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
  match non_bottomb x as b return (b = true -> non_bottom x) -> option non_empty with
  | true => fun H => Some (exist _ x (H eq_refl))
  | false => fun _ => None
  end (elimT (non_bottombP x)).

(* Everything the laws below need to know about [to_non_empty], proved once:
   reasoning about the dependent match takes the same two steps every time —
   generalize the [elimT] argument, which is what removes [non_bottombP x] from
   the goal, then [case] on [non_bottomb x] to reduce the match. *)
Lemma to_non_emptyP x :
  if to_non_empty x is Some y then `y = x else ~ non_bottom x.
Proof.
  rewrite /to_non_empty; move: (elimT (non_bottombP x)) (elimF (non_bottombP x)).
  by case: (non_bottomb x) => // _ H; apply: H.
Qed.

Lemma to_non_empty_none : forall x, to_non_empty x = None -> gamma_pe x ⊆⊇ ∅.
Proof.
  move=> x; move: (to_non_emptyP x).
  by case: (to_non_empty x) => // H _; apply: non_bottom_empty.
Qed.

Lemma to_non_empty_some : forall x y, to_non_empty x = Some y -> gamma_ne y ⊆⊇ gamma_pe x.
Proof.
  move=> x y; move: (to_non_emptyP x).
  by case: (to_non_empty x) => // z <- [<-]; apply: gamma_nbitv_gamma_itv_set.
Qed.

Definition singleton_sound : forall k, (k ∈ gamma_ne (singleton k)).
Proof.
  intros k. unfold gamma_ne, singleton.
  rewrite gamma_nbitv_gamma_itv. apply gamma_itv_singleton.
Qed.

Definition equiv (a b : non_empty) : bool := ZInterval.equiv (`a) (`b).
Definition join (a b : non_empty) : non_empty :=
  exist _ (ZInterval.join (`a) (`b)) (itv_join_non_bottom (`a) (`b) (proj2_sig a) (proj2_sig b)).
Definition meet (a b : non_empty) : possibly_empty := ZInterval.meet (`a) (`b).
