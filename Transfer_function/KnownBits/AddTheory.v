(* AddTheory.v - precision theory for the [Z.add] transfer function on the
   KnownBits single-value abstraction. The operation itself ([kb_add]) and
   its positive properties (soundness, best abstraction: [kb_add_best])
   live in [KnownBits.v]; this file collects the *negative* precision
   results delimiting them. *)

(* STATUS: add: sound + best (proved in KnownBits.v, [kb_add_best]);
   NOT γ-exact ([kb_add_not_exact]);
   NOT α-complete ([kb_add_not_alpha_complete], witness
   S1 = {16,20,32,36}, S2 = {16,17}). *)

From Stdlib Require Import ssreflect ssrbool.
Require Import Stdlib.ZArith.ZArith.
From Stdlib Require Import Lia.
Require Import base Abstraction Quadrivalent KnownBits.
Open Scope Z_scope.

(** Bit [i ≥ 2] of the literal [2] is [0] (companion to [testbit_3_SS] in
    [KnownBits.v]). *)
Lemma testbit_2_SS i : testbit 2 (S (S i)) = false.
Proof.
  rewrite /testbit. apply Z.bits_above_log2; try lia.
  have : (Z.log2 2 = 1)%Z by []. lia.
Qed.

(** ** [kb_add] is not exact (γ-complete).

    Witness: the two-low-bits-unknown element [a] with γ(a) = {0,1,2,3}.
    [kb_add a a] leaves bits {0,1,2} unknown, so [7 ∈ γ(kb_add a a)] — but
    no sum [p+q] with [p,q ∈ {0,1,2,3}] reaches 7 (the maximum is 3+3=6).
    This is not a defect of [kb_add]: it is the *best* transfer function
    ([kb_add_best]); the set {0,…,6} simply is not representable. *)

(** The two-low-bits-unknown value: [must0 = 0b11], [must1 = 0];
    γ = {0,1,2,3}. *)
Definition kb_two_unknown : must0_must1 := {| must0 := 3; must1 := 0 |}.

Lemma kb_two_unknown_membership v :
  v ∈ γ[kb_abs] kb_two_unknown <-> (v = 0 \/ v = 1 \/ v = 2 \/ v = 3).
Proof.
  rewrite kb_gamma_impl. split.
  - move=> H.
    have Hhi : forall i : nat, testbit v (S (S i)) = false.
    { move=> i. have [H0 _] := H (S (S i)). apply H0. apply testbit_3_SS. }
    case Hb0 : (testbit v 0%nat); case Hb1 : (testbit v 1%nat).
    + right; right; right. apply Z_testbit_ext => -[|[|i]].
      * by rewrite Hb0 testbit_3_0.
      * by rewrite Hb1 testbit_3_1.
      * by rewrite Hhi testbit_3_SS.
    + right; left. apply Z_testbit_ext => -[|[|i]].
      * by rewrite Hb0 testbit_1_0.
      * by rewrite Hb1 testbit_1_S.
      * by rewrite Hhi testbit_1_S.
    + right; right; left. apply Z_testbit_ext => -[|[|i]].
      * by rewrite Hb0 testbit_2_0.
      * by rewrite Hb1 testbit_2_1.
      * by rewrite Hhi testbit_2_SS.
    + left. apply Z_testbit_ext => -[|[|i]].
      * by rewrite Hb0 testbit_0.
      * by rewrite Hb1 testbit_0.
      * by rewrite Hhi testbit_0.
  - move=> Hv i. rewrite /kb_two_unknown /must0 /must1. split.
    + move=> Hm0. move: Hm0. case: i => [|[|i]].
      * by rewrite testbit_3_0.
      * by rewrite testbit_3_1.
      * move=> _. case: Hv => [->|[->|[->|->]]].
        -- apply testbit_0.
        -- apply testbit_1_S.
        -- apply testbit_2_SS.
        -- apply testbit_3_SS.
    + by rewrite testbit_0.
Qed.

Lemma kb_add_two_unknown_compute :
  kb_add kb_two_unknown kb_two_unknown = {| must0 := 7; must1 := 0 |}.
Proof. by vm_compute. Qed.

(** The best transfer function [kb_add] is NOT exact (γ-complete):
    for [a = α {0,1,2,3}], [7 ∈ γ(kb_add a a)] but 7 is no sum [p+q]
    with [p,q ∈ {0,1,2,3}] (max 3+3 = 6). *)
Lemma kb_add_not_exact_witness :
  γ[kb_abs] (kb_add kb_two_unknown kb_two_unknown)
    ⊆⊇ collecting_binary_forward Z.add
          (γ[kb_abs] kb_two_unknown) (γ[kb_abs] kb_two_unknown)
  -> False.
Proof.
  move=> [Hsub _].
  have H7 : 7 ∈ γ[kb_abs] (kb_add kb_two_unknown kb_two_unknown).
  { rewrite kb_add_two_unknown_compute kb_gamma_impl => i.
    rewrite /must0 /must1. split.
    - by [].
    - by rewrite testbit_0. }
  have H7' := Hsub _ H7.
  have [p [q [Hp [Hq Hpq]]]] :
    exists p q, p ∈ γ[kb_abs] kb_two_unknown
             /\ q ∈ γ[kb_abs] kb_two_unknown /\ p + q = 7.
  { move: H7'. rewrite /collecting_binary_forward. by unfold_set. }
  rewrite kb_two_unknown_membership in Hp.
  rewrite kb_two_unknown_membership in Hq.
  destruct Hp as [-> | [-> | [-> | ->]]]; destruct Hq as [-> | [-> | [-> | ->]]]; lia.
Qed.

Lemma kb_add_not_exact :
  ~ binary_exact kb_ad kb_ad kb_ad kb_add (collecting_binary_forward Z.add).
Proof.
  move=> Hexact. apply kb_add_not_exact_witness.
  exact: (Hexact kb_two_unknown kb_two_unknown).
Qed.

(** ** [kb_add] is not α-complete.

    Being best ([kb_add_best]) means: the result is the α of the sum of
    the operands' *concretizations*. α-completeness asks for more: when the
    operands are the α's of arbitrary concrete sets [S1], [S2], the result
    should be the α of [S1 + S2]. [kb_add] fails this because abstracting
    an operand can inflate it (γ(α S) ⊋ S), and the sum of the inflated
    sets admits a strictly better abstraction than the sum of the originals.

    Witness: [S1 = {16,20,32,36}] (α = bits {2,4,5} unknown, γ inflates to
    8 values) and [S2 = {16,17}] (α exact). Every element of [S1 + S2] has
    bit 5 set, so the best abstraction of the sum forces bit 5 — but
    [kb_add (α S1) (α S2)] leaves bit 5 unknown: e.g. [16] remains in its
    concretization. *)

(** *** Generic small lemmas *)

(** Bits at positions [i ≥ n] of a small nonnegative constant are 0. *)
Lemma testbit_small (v : Z) (n i : nat) :
  0 <= v -> Z.log2 v < Z.of_nat n -> (n <= i)%nat ->
  testbit v i = false.
Proof.
  move=> H0 Hlog Hle. rewrite /testbit. apply Z.bits_above_log2 => //.
  apply: (Z.lt_le_trans _ (Z.of_nat n)) => //. lia.
Qed.

(** Sufficient condition for γ-membership by computation on the masks:
    [v] is in [γ kb] as soon as [v] is bitwise below [must0] and above
    [must1]. Converse of [kb_gamma_land_must0] / [kb_gamma_lor_must1];
    for literal [v] and [kb] both premises are closed computations. *)
Lemma kb_gamma_of_land_lor (kb : must0_must1) (v : Z) :
  Z.land v (must0 kb) = v -> Z.lor v (must1 kb) = v ->
  v ∈ γ[kb_abs] kb.
Proof.
  move=> Hland Hlor. rewrite kb_gamma_impl => i. split.
  - move=> Hm0. have H := f_equal (fun z => testbit z i) Hland.
    rewrite testbit_land Hm0 andbF in H. by rewrite -H.
  - move=> Hm1. have H := f_equal (fun z => testbit z i) Hlor.
    rewrite testbit_lor Hm1 orbT in H. by rewrite -H.
Qed.

(** The three shapes of a per-bit exactness obligation over a set [S]:
    the bit is 0 throughout [S], 1 throughout [S], or attains both. *)

Lemma perbit_false (S : ℘ Z) (i : nat) (w : Z) :
  w ∈ S ->
  (forall v, v ∈ S -> testbit v i = false) ->
  ExactlyRepresents (A := qv_abs) QFalse
    (collecting_forward (fun v => testbit v i) S).
Proof.
  move=> Hw Hall. split.
  - move=> b. unfold_set. move=> ->.
    exists w. split; [exact: Hw | exact: (Hall w Hw)].
  - move=> b. unfold_set. move=> [v [Hv Heq]].
    rewrite -Heq. exact: (Hall v Hv).
Qed.

Lemma perbit_true (S : ℘ Z) (i : nat) (w : Z) :
  w ∈ S ->
  (forall v, v ∈ S -> testbit v i = true) ->
  ExactlyRepresents (A := qv_abs) QTrue
    (collecting_forward (fun v => testbit v i) S).
Proof.
  move=> Hw Hall. split.
  - move=> b. unfold_set. move=> ->.
    exists w. split; [exact: Hw | exact: (Hall w Hw)].
  - move=> b. unfold_set. move=> [v [Hv Heq]].
    rewrite -Heq. exact: (Hall v Hv).
Qed.

Lemma perbit_top (S : ℘ Z) (i : nat) (w0 w1 : Z) :
  w0 ∈ S -> testbit w0 i = false ->
  w1 ∈ S -> testbit w1 i = true ->
  ExactlyRepresents (A := qv_abs) QTop
    (collecting_forward (fun v => testbit v i) S).
Proof.
  move=> Hw0 Hb0 Hw1 Hb1. split.
  - move=> b. unfold_set. move=> _. case: b.
    + exists w1. by split.
    + exists w0. by split.
  - move=> b. by unfold_set.
Qed.

(** *** The witness operands and their [IsAlpha] proofs *)

(** [S1 = {16, 20, 32, 36}]: bits 2, 4, 5 vary, all other bits are 0. *)
Definition set1 : ℘ Z := {[ x | x = 16 \/ x = 20 \/ x = 32 \/ x = 36 ]}.

(** [S2 = {16, 17}]: bit 4 always set, bit 0 varies. *)
Definition set2 : ℘ Z := {[ x | x = 16 \/ x = 17 ]}.

(** α(S1): bits {2,4,5} unknown ([must0 = 52]), nothing forced to 1.
    Note γ(kb_a1) = {0,4,16,20,32,36,48,52} ⊋ S1: the abstraction is not
    exact for [set1], which is exactly what the counterexample exploits. *)
Definition kb_a1 : must0_must1 := {| must0 := 52; must1 := 0 |}.

(** α(S2): bit 4 forced to 1, bit 0 unknown. Here γ(kb_a2) = S2. *)
Definition kb_a2 : must0_must1 := {| must0 := 17; must1 := 16 |}.

Lemma kb_a1_nb : kb_non_bottom kb_a1.
Proof.
  move=> i. rewrite /kb_testbit /= ?testbit_0.
  by case: (testbit 52 i).
Qed.

Lemma kb_a2_nb : kb_non_bottom kb_a2.
Proof.
  move=> i. rewrite /kb_testbit /=.
  case: i => [|[|[|[|[|i]]]]] => //=.
  have -> : testbit 17 (S (S (S (S (S i))))) = false
    by apply: (testbit_small _ 5) => //; lia.
  have -> : testbit 16 (S (S (S (S (S i))))) = false
    by apply: (testbit_small _ 5) => //; lia.
  by [].
Qed.

Lemma kb_a1_alpha : IsAlpha (A := kb_ad) kb_a1 set1.
Proof.
  apply (kb_is_alpha_of_perbit (exist _ kb_a1 kb_a1_nb)) => i /=.
  have Hmem : forall x, x = 16 \/ x = 20 \/ x = 32 \/ x = 36 -> x ∈ set1.
  { move=> x Hx. by unfold_set. }
  case: i => [|[|[|[|[|[|i]]]]]].
  - (* bit 0: 0 throughout *)
    apply: (perbit_false _ _ 16); first by apply Hmem; tauto.
    move=> v. unfold_set. by move=> [->|[->|[->|->]]].
  - (* bit 1: 0 throughout *)
    apply: (perbit_false _ _ 16); first by apply Hmem; tauto.
    move=> v. unfold_set. by move=> [->|[->|[->|->]]].
  - (* bit 2: 0 on 16, 1 on 20 *)
    by apply: (perbit_top _ _ 16 20) => //; apply Hmem; tauto.
  - (* bit 3: 0 throughout *)
    apply: (perbit_false _ _ 16); first by apply Hmem; tauto.
    move=> v. unfold_set. by move=> [->|[->|[->|->]]].
  - (* bit 4: 1 on 16, 0 on 32 *)
    by apply: (perbit_top _ _ 32 16) => //; apply Hmem; tauto.
  - (* bit 5: 0 on 16, 1 on 32 *)
    by apply: (perbit_top _ _ 16 32) => //; apply Hmem; tauto.
  - (* bits ≥ 6: 0 throughout *)
    have Hb52 : testbit 52 (S (S (S (S (S (S i)))))) = false
      by apply: (testbit_small _ 6) => //; lia.
    have -> : kb_testbit kb_a1 (S (S (S (S (S (S i)))))) = QFalse
      by rewrite /kb_testbit /= Hb52 ?testbit_0.
    apply: (perbit_false _ _ 16); first by apply Hmem; tauto.
    move=> v. unfold_set.
    by move=> [->|[->|[->|->]]]; apply: (testbit_small _ 6) => //; lia.
Qed.

Lemma kb_a2_alpha : IsAlpha (A := kb_ad) kb_a2 set2.
Proof.
  apply (kb_is_alpha_of_perbit (exist _ kb_a2 kb_a2_nb)) => i /=.
  have Hmem : forall x, x = 16 \/ x = 17 -> x ∈ set2.
  { move=> x Hx. by unfold_set. }
  case: i => [|[|[|[|[|i]]]]].
  - (* bit 0: 0 on 16, 1 on 17 *)
    by apply: (perbit_top _ _ 16 17) => //; apply Hmem; tauto.
  - (* bit 1: 0 throughout *)
    apply: (perbit_false _ _ 16); first by apply Hmem; tauto.
    move=> v. unfold_set. by move=> [->|->].
  - (* bit 2: 0 throughout *)
    apply: (perbit_false _ _ 16); first by apply Hmem; tauto.
    move=> v. unfold_set. by move=> [->|->].
  - (* bit 3: 0 throughout *)
    apply: (perbit_false _ _ 16); first by apply Hmem; tauto.
    move=> v. unfold_set. by move=> [->|->].
  - (* bit 4: 1 throughout *)
    apply: (perbit_true _ _ 16); first by apply Hmem; tauto.
    move=> v. unfold_set. by move=> [->|->].
  - (* bits ≥ 5: 0 throughout *)
    have Hb17 : testbit 17 (S (S (S (S (S i))))) = false
      by apply: (testbit_small _ 5) => //; lia.
    have -> : kb_testbit kb_a2 (S (S (S (S (S i))))) = QFalse.
    { rewrite /kb_testbit /= Hb17.
      have -> : testbit 16 (S (S (S (S (S i))))) = false
        by apply: (testbit_small _ 5) => //; lia.
      by []. }
    apply: (perbit_false _ _ 16); first by apply Hmem; tauto.
    move=> v. unfold_set.
    by move=> [->|->]; apply: (testbit_small _ 5) => //; lia.
Qed.

(** *** The refutation *)

(** The best abstraction of [S1 + S2 = {32,33,36,37,48,49,52,53}]: bit 5
    forced to 1, bits {0,2,4} unknown. We only need that it encloses the
    sum while excluding 16. *)
Definition kb_sum_best : must0_must1 := {| must0 := 53; must1 := 32 |}.

Lemma sum_in_best :
  collecting_binary_forward Z.add set1 set2 ⊆ γ[kb_abs] kb_sum_best.
Proof.
  move=> x Hx.
  have [p [q [Hp [Hq Heq]]]] :
    exists p q, (p = 16 \/ p = 20 \/ p = 32 \/ p = 36)
             /\ (q = 16 \/ q = 17) /\ p + q = x.
  { move: Hx. rewrite /set1 /set2. by unfold_set. }
  subst x.
  case: Hp => [->|[->|[->|->]]]; case: Hq => [->|->];
    apply: kb_gamma_of_land_lor; by vm_compute.
Qed.

Lemma kb_add_a1_a2_compute :
  kb_add kb_a1 kb_a2 = {| must0 := 117; must1 := 0 |}.
Proof. by vm_compute. Qed.

(** [kb_add] is not α-complete at the witness: [kb_a1], [kb_a2] are the
    best abstractions of [set1], [set2], yet [kb_add kb_a1 kb_a2] is not
    the best abstraction of [set1 + set2] — the competitor [kb_sum_best]
    encloses the sum but not [γ (kb_add kb_a1 kb_a2) ∋ 16]. *)
Lemma kb_add_not_alpha_complete_witness :
  ~ binary_alpha_complete kb_ad kb_ad kb_ad kb_add
      (collecting_binary_forward Z.add) kb_a1 kb_a2 set1 set2.
Proof.
  move=> Hac.
  have Halpha := Hac kb_a1_alpha kb_a2_alpha.
  have Hle : kb_add kb_a1 kb_a2 ⊑[kb_ad] kb_sum_best.
  { apply (proj1 (Halpha kb_sum_best)). exact: sum_in_best. }
  have H16 : 16 ∈ γ[kb_abs] (kb_add kb_a1 kb_a2).
  { rewrite kb_add_a1_a2_compute.
    apply: kb_gamma_of_land_lor; by vm_compute. }
  have H16' : 16 ∈ γ[kb_abs] kb_sum_best.
  { exact: (kb_sqsubseteq_sound _ _ Hle _ H16). }
  move/kb_gamma_impl/(_ 5%nat): H16' => [_ H1].
  by move: (H1 (eq_refl _)).
Qed.

(** Headline form: [kb_add] does not satisfy [binary_alpha_complete]
    universally (although it is sound and best, [kb_add_best]). *)
Lemma kb_add_not_alpha_complete :
  ~ (forall (a2 a1 : must0_must1) (S2 S1 : ℘ Z),
       binary_alpha_complete kb_ad kb_ad kb_ad kb_add
         (collecting_binary_forward Z.add) a2 a1 S2 S1).
Proof.
  move=> H. exact: (kb_add_not_alpha_complete_witness (H kb_a1 kb_a2 set1 set2)).
Qed.
