(* EqbTheory.v - [Z.eqb] transfer function for the ZInterval single-value
   abstraction: [interval_eqb] takes two intervals and returns a
   [quadrivalent]. Split out of Z_interval.v. *)

(* STATUS: eqb (Z.eqb): exact
     (nbinterval_eqb_unopt_exact, may_be_{true,false}_eqb_exact).
   Two variants are provided: the naive [interval_eqb_unopt] and the
   optimized [interval_eqb_opt], proved equal. *)

Require Import Abstraction AbstractLattice.
Require Import ssreflect ssrbool ssrfun.
Require Import BoundAbstraction.
Require Import AbstractionCombination.
Require Import BoundLattice.
Require Import autoreflect.
Require Import Tactics.
Require Import Stdlib.Bool.Bool.
Require Import Quadrivalent.
From Stdlib Require Import Lia. (* lia/nia; avoid Psatz which loads Reals axioms *)
Require Import Stdlib.ZArith.ZArith.
Require Import Z_interval.
Open Scope Z_scope.
Generalizable All Variables.

(** * Interval equality: abstract Z.eqb *)

Section Interval_eqb.

(** Whether Z.eqb c2 c1 = true is possible: need c2 = c1,
    i.e. the intervals [l1,h1] and [l2,h2] overlap.
    Disjoint iff h1 < l2 or h2 < l1. *)
Definition may_be_true_eqb (l1 h1 l2 h2 : WithTop.with_top Z) : bool :=
  match l2, h1 with
  | WithTop.NotTop l2', WithTop.NotTop h1' => Z.leb l2' h1'
  | _, _ => true
  end &&
  match l1, h2 with
  | WithTop.NotTop l1', WithTop.NotTop h2' => Z.leb l1' h2'
  | _, _ => true
  end.

Lemma may_be_true_eqb_exact l1 h1 l2 h2:
  non_bottom (l1, h1) -> non_bottom (l2, h2) ->
  (may_be_true_eqb l1 h1 l2 h2 = true <->
   exists c2 c1, c2 ∈ γ[itv] (l2, h2) /\ c1 ∈ γ[itv] (l1, h1) /\ Z.eqb c2 c1 = true).
Proof.
  move => Hnb1 Hnb2.
  apply non_bottom_non_empty in Hnb1 as [w1 [Hw1l Hw1h]].
  apply non_bottom_non_empty in Hnb2 as [w2 [Hw2l Hw2h]].
  destruct (may_be_true_eqb l1 h1 l2 h2) eqn:Hmb.
  - suffices: exists c2 c1 : Z,
        c2 ∈ (γ[ itv] ) (l2, h2) /\ c1 ∈ (γ[ itv] ) (l1, h1) /\ (c2 =? c1) = true by tauto.
    rewrite /may_be_true_eqb in Hmb.
    destruct l1 as [|l1']; destruct h1 as [|h1'];
      destruct l2 as [|l2']; destruct h2 as [|h2']; unfold_set in *; simpl in *.
    all: try (exists l2', l2'; lia).
    all: try (exists h2', h2'; lia).
    all: try (exists 0, 0; lia).
    all: try (exists h1', h1'; lia).
    all: try (exists l1', l1'; lia).
    all: try (exists (Z.min h1' h2'), (Z.min h1' h2'); lia).
    all: try (exists (Z.max l1' l2'), (Z.max l1' l2'); lia).
  - suffices H: not (exists c2 c1 : Z,
                      c2 ∈ (γ[ itv] ) (l2, h2) /\ c1 ∈ (γ[ itv] ) (l1, h1) /\ (c2 =? c1) = true).
    { split; move=> H2; [discriminate|exfalso; by apply H]. }
    move => [c2 [c1 [Hc2 [Hc1 Heq]]]].
    apply Z.eqb_eq in Heq. subst c1.
    unfold_set in Hc1; unfold_set in Hc2.
    destruct l1 as [|l1']; destruct h1 as [|h1'];
      destruct l2 as [|l2']; destruct h2 as [|h2'];
      rewrite /may_be_true_eqb in Hmb;
      simpl in *; unfold_set in *; lia.
Qed.

Definition may_be_false_eqb (l1 h1 l2 h2 : WithTop.with_top Z) : bool :=
  match is_singleton l1 h1, is_singleton l2 h2 with
  | Some x1, Some x2 => negb (Z.eqb x1 x2)
  | _, _ => true
  end. 

Lemma may_be_false_eqb_exact l1 h1 l2 h2:
  non_bottom (l1, h1) -> non_bottom (l2, h2) ->
  (may_be_false_eqb l1 h1 l2 h2 = true <->
   exists c2 c1, c2 ∈ γ[itv] (l2, h2) /\ c1 ∈ γ[itv] (l1, h1) /\ Z.eqb c2 c1 = false).
Proof.
  move=> Hnb1 Hnb2.
  destruct (may_be_false_eqb l1 h1 l2 h2) eqn:Hmb.
  - suffices: exists c2 c1, c2 ∈ γ[itv] (l2, h2)
                         /\ c1 ∈ γ[itv] (l1, h1) /\ (c2 =? c1) = false by tauto.
    move: Hmb. rewrite /may_be_false_eqb.
    case Hs2: (is_singleton l2 h2) => [x2|] Hmb.
    + (* γ2 = {x2}; pick c1 ∈ γ1 with c1 ≠ x2 *)
      have Hns1 : is_singleton l1 h1 <> Some x2.
      { move: Hmb. case: (is_singleton l1 h1) => [x1|//].
        move=> /negbTE/Z.eqb_neq Hne [?]. by subst. }
      have [c1 [Hc1 Hne]] := is_singleton_witness_not_x _ _ _ Hnb1 Hns1.
      move/is_singleton_spec: Hs2 => Hs2.
      exists x2, c1; split; [by apply Hs2|split=> //].
      apply/Z.eqb_neq; lia.
    + (* γ2 has multiple elements; any c1 works. *)
      have [c1 Hc1] := proj1 (non_bottom_non_empty _) Hnb1.
      have Hns2 : is_singleton l2 h2 <> Some c1 by rewrite Hs2.
      have [c2 [Hc2 Hne]] := is_singleton_witness_not_x _ _ _ Hnb2 Hns2.
      exists c2, c1; split=> //; split=> //. by apply/Z.eqb_neq.
  - suffices H: not (exists c2 c1, c2 ∈ γ[itv] (l2, h2)
                                /\ c1 ∈ γ[itv] (l1, h1) /\ (c2 =? c1) = false).
    { split; [discriminate|move=> H'; exfalso; by apply H]. }
    move=> [w2 [w1 [Hw2 [Hw1 Heq]]]].
    suffices: (w2 = w1). 
    { move => ?; subst. by rewrite Z.eqb_refl in Heq. }
    clear Heq.
    rewrite /may_be_false_eqb in Hmb.
    destruct (is_singleton l1 h1) as [x1|] eqn:Hs1 => //.
    destruct (is_singleton l2 h2) as [x2|] eqn:Hs2 => //.
    move: Hmb => /negbFE /Z.eqb_eq ?; subst x2.
    move/is_singleton_spec: Hs1 => Hs1; move/is_singleton_spec: Hs2 => Hs2.
    have: w1 = x1 by apply Hs1. 
    have: w2 = x1 by apply Hs2.
    congruence.
Qed.

(** Naive [interval_eqb]: just combine [may_be_true_eqb] and
    [may_be_false_eqb] via [to_quadrivalent]. Easy to prove correct,
    but evaluates both sides even when the result is forced. A more
    efficient [interval_eqb_opt] (decision tree with shortcuts) can
    be defined separately and proved equivalent by case analysis. *)
Definition interval_eqb_unopt (i2 i1 : interval) : quadrivalent :=
  let (l2, h2) := i2 in
  let (l1, h1) := i1 in
  to_quadrivalent (may_be_true_eqb l1 h1 l2 h2) (may_be_false_eqb l1 h1 l2 h2).

Definition nbinterval_eqb_unopt (i2 i1 : nb_interval) : quadrivalent :=
  interval_eqb_unopt (`i2) (`i1).

Lemma nbinterval_eqb_unopt_exact:
  binary_exact nbitv nbitv qv nbinterval_eqb_unopt
    (collecting_binary_forward Z.eqb).
Proof.
  move=> [[l2 h2] P2] [[l1 h1] P1].
  unfold nbinterval_eqb_unopt, interval_eqb_unopt. simpl.
  unfold ExactlyRepresents. to_set.
  have HU := unfold_set_equiv. unfold_set. clear HU.
  move=> c. case: c.
  - rewrite to_quadrivalent_true.
    rewrite (may_be_true_eqb_exact _ _ _ _ P1 P2).
    by split; move=> [c2 [c1 H]]; exists c2, c1; unfold_set in *.
  - rewrite to_quadrivalent_false.
    rewrite (may_be_false_eqb_exact _ _ _ _ P1 P2).
    by split; move=> [c2 [c1 H]]; exists c2, c1; unfold_set in *.
Qed.

(** Optimized [interval_eqb]: skip the [may_be_false_eqb] machinery
    (i.e. the singleton-equality test) when at least one side is not
    a singleton — in that situation [may_be_false_eqb] is always
    [true], so the result is fully determined by the overlap test. *)
Definition interval_eqb_opt (i2 i1 : interval) : quadrivalent :=
  let (l2, h2) := i2 in
  let (l1, h1) := i1 in
  match is_singleton l1 h1, is_singleton l2 h2 with
  | Some x1, Some x2 => if Z.eqb x1 x2 then QTrue else QFalse
  | _, _ => if may_be_true_eqb l1 h1 l2 h2 then QTop else QFalse
  end.

Lemma interval_eqb_opt_eq i2 i1 :
  interval_eqb_opt i2 i1 = interval_eqb_unopt i2 i1.
Proof.
  case: i2 => l2 h2; case: i1 => l1 h1.
  rewrite /interval_eqb_opt /interval_eqb_unopt /may_be_false_eqb.
  case Hs1: (is_singleton l1 h1) => [x1|];
  case Hs2: (is_singleton l2 h2) => [x2|];
    try by case: (may_be_true_eqb l1 h1 l2 h2).
  (* both singletons: unfold and reduce. *)
  move: Hs1 Hs2. rewrite /is_singleton.
  case: l1 => [//|l1']; case: h1 => [//|h1'].
  case: l2 => [//|l2']; case: h2 => [//|h2'].
  case: (Z.eqb_spec l1' h1') => [<-|//].
  case: (Z.eqb_spec l2' h2') => [<-|//].
  move=> [->] [->].
  rewrite /may_be_true_eqb /to_quadrivalent /=.
  case: (Z.eqb_spec x1 x2) => [<-|Hne] /=.
  - by rewrite !Z.leb_refl.
  - have -> : (x2 <=? x1) && (x1 <=? x2) = false.
    { case: (Z.leb_spec x2 x1); case: (Z.leb_spec x1 x2) => //=; lia. }
    done.
Qed.

End Interval_eqb.
