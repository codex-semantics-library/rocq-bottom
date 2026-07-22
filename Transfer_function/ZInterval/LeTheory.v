(* LeTheory.v - [Z.leb] transfer function for the ZInterval single-value
   abstraction: [interval_leb] takes two intervals and returns a
   [quadrivalent]. Split out of Z_interval.v. *)

(* STATUS: leb (Z.leb): exact (nbinterval_leb_exact). *)

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
Require Import ZIntervalComp.
Require Import ZIntervalTheory.
Require Import Transfer_function.ZInterval.OpsComp.
Open Scope Z_scope.
Generalizable All Variables.

(** * Interval comparison: abstract Z.leb *)

Section Interval_leb.


Lemma nbinterval_leb_exact:
  binary_exact nbitv nbitv qv nbinterval_leb
    (collecting_binary_forward Z.leb).
Proof.
  move=> [[l2 h2] P2] [[l1 h1] P1]. unfold nbinterval_leb,interval_leb. simpl.
  unfold ExactlyRepresents. to_set. 
  have HU := unfold_set_equiv. unfold_set. clear HU.
  apply non_bottom_non_empty in P1. destruct P1 as [w1 H1].
  apply non_bottom_non_empty in P2. destruct P2 as [w2 H2].
  move => c. case: c.
  - rewrite to_quadrivalent_true. unfold may_be_true_leb.
    setoid_rewrite Z.leb_le.
    destruct l2 as [|l2].
    + split => //; move => _.
      exists (Z.min w2 w1), w1.
      unfold_set in H1; simpl in H1.
      repeat split; try (tauto||lia).
      * destruct h2; simpl => //. unfold_set. unfold_set in H2; simpl in H2. lia.
    + destruct h1 as [|h1].
      * split => //; move => _.
        unfold_set in H2; simpl in H2.
        exists w2, (Z.max w2 w1). simpl. repeat split; try (tauto||lia).
        -- destruct l1; simpl => //. unfold_set in H1; simpl in H1. unfold_set. lia.
      * setoid_rewrite Z.leb_le. simpl.
        split. move=> Hl2l1.
        -- exists l2,h1. unfold_set. repeat split => //.
           ++ lia.
           ++ destruct h2 => //; simpl. unfold_set in H2. simpl in H2. unfold_set. lia.
           ++ destruct l1 => //. unfold_set. unfold_set in H1; simpl in H1. lia.
           ++ reflexivity.
        -- move => [c2 [c1 H]]. unfold_set in H. lia.
  - rewrite to_quadrivalent_false. unfold may_be_false_leb.
    destruct h2 as [|h2].
    + split => //; move => _.
      exists (Z.max w2 (w1 + 1)), w1. unfold_set. repeat split.
      * destruct l2; unfold_set; simpl => //. unfold_set in H2; simpl in H2. lia.
      * destruct l1; unfold_set; simpl => //. unfold_set in H1; simpl in H1. lia.
      * unfold_set. unfold_set in H1. simpl in H1. tauto.
      * apply Z.leb_gt. lia.
    + destruct l1 as [|l1].
      (* l1 = Top, h2 = NotTop h2 *)
      * split => //; move => _.
        exists w2, (Z.min w2 w1 - 1). repeat split.
        all: destruct l2; destruct h1;
             unfold_set in H2; unfold_set in H1; unfold_set;
             simpl in *; try tauto; try lia.
        all: try (apply Z.leb_gt; lia).
      (* l1 = NotTop l1, h2 = NotTop h2 *)
      * split.
        -- case: (Z.leb_spec h2 l1) => // Hh2l1 _.
           exists h2, l1.
           destruct l2; destruct h1;
             unfold_set in H2; unfold_set in H1; unfold_set;
             simpl in *; repeat split; try tauto; try lia.
           all: apply Z.leb_gt; lia.
        -- move => [c2 [c1 H]].
           destruct l2; destruct h1;
             unfold_set in H; simpl in H.
           all: apply negb_true_iff; apply Z.leb_gt; lia.
Qed.

End Interval_leb.
