(* BitwiseTheory.v - the bitwise transfer functions [kb_lor] / [kb_land] /
   [kb_lxor] on the KnownBits single-value abstraction. Grouped in one file
   because all three are instances of the same generic per-bit argument
   ([kb_bitwise_perbit_sound], [kb_bitwise_sound], [kb_bitwise_underapprox]).
   Split out of KnownBits.v. *)

(* STATUS: lor, land, lxor: sound + exact (γ-complete), hence best
     (kb_{lor,land,lxor}_sound, kb_{lor,land,lxor}_exact).
   Being exact, they are also α-complete: the per-bit quadrivalent
   operations lose nothing. *)

From Stdlib Require Import ssreflect ssrbool.
Require Import Stdlib.ZArith.ZArith.
From Stdlib Require Import Lia. (* lia/nia; avoid Psatz which loads Reals axioms *)
Require Import base Abstraction AbstractionCombination Quadrivalent KnownBits.
Open Scope Z_scope.

(** ** Bitwise transfer functions *)

Require Import SvaQuadrivalent.

(** *** Definitions *)

Definition kb_lor (kb1 kb2 : must0_must1) : must0_must1 :=
  {| must0 := Z.lor (must0 kb1) (must0 kb2);
     must1 := Z.lor (must1 kb1) (must1 kb2) |}.

Definition kb_land (kb1 kb2 : must0_must1) : must0_must1 :=
  {| must0 := Z.land (must0 kb1) (must0 kb2);
     must1 := Z.land (must1 kb1) (must1 kb2) |}.

Definition kb_lxor (kb1 kb2 : must0_must1) : must0_must1 :=
  let xor00 := Z.lxor (must0 kb1) (must0 kb2) in
  let xor11 := Z.lxor (must1 kb1) (must1 kb2) in
  let unknown := Z.lxor (must0 kb1) (must1 kb1) in
  {| must0 := Z.lor (Z.lor xor00 xor11) unknown;
     must1 := Z.land xor00 xor11 |}.

(** *** Per-bit correspondence with quadrivalent operations (non-bottom) *)

Lemma kb_testbit_lor kb1 kb2 i :
  kb_testbit kb1 i <> QBottom ->
  kb_testbit kb2 i <> QBottom ->
  kb_testbit (kb_lor kb1 kb2) i = abs_orb (kb_testbit kb1 i) (kb_testbit kb2 i).
Proof.
  rewrite /kb_testbit /kb_lor /= testbit_lor testbit_lor.
  by case_kb2_testbit kb1 kb2 i.
Qed.

Lemma kb_testbit_land kb1 kb2 i :
  kb_testbit kb1 i <> QBottom ->
  kb_testbit kb2 i <> QBottom ->
  kb_testbit (kb_land kb1 kb2) i = abs_andb (kb_testbit kb1 i) (kb_testbit kb2 i).
Proof.
  rewrite /kb_testbit /kb_land /= testbit_land testbit_land.
  by case_kb2_testbit kb1 kb2 i.
Qed.

Lemma kb_testbit_lxor kb1 kb2 i :
  kb_testbit kb1 i <> QBottom ->
  kb_testbit kb2 i <> QBottom ->
  kb_testbit (kb_lxor kb1 kb2) i = abs_xorb (kb_testbit kb1 i) (kb_testbit kb2 i).
Proof.
  rewrite /kb_testbit /kb_lxor /= testbit_lor testbit_lor testbit_land
    !testbit_lxor.
  by case_kb2_testbit kb1 kb2 i.
Qed.

(** *** Generic bitwise soundness *)

(** Per-bit soundness from kb_testbit correspondence + qv soundness. *)
Lemma kb_bitwise_perbit_sound
  (bop : bool -> bool -> bool)
  (kbop : must0_must1 -> must0_must1 -> must0_must1)
  (qvop : quadrivalent -> quadrivalent -> quadrivalent)
  (Hkbop : forall kb1 kb2 i,
    kb_testbit kb1 i <> QBottom -> kb_testbit kb2 i <> QBottom ->
    kb_testbit (kbop kb1 kb2) i = qvop (kb_testbit kb1 i) (kb_testbit kb2 i))
  (Hqvop : forall q1 q2 b1 b2,
    b1 ∈ γ[qv_abs] q1 -> b2 ∈ γ[qv_abs] q2 ->
    bop b1 b2 ∈ γ[qv_abs] (qvop q1 q2))
  : forall kb1 kb2 i b1 b2,
    b1 ∈ γ[qv_abs] (kb_testbit kb1 i) ->
    b2 ∈ γ[qv_abs] (kb_testbit kb2 i) ->
    bop b1 b2 ∈ γ[qv_abs] (kb_testbit (kbop kb1 kb2) i).
Proof.
  move=> kb1 kb2 i b1 b2 Hb1 Hb2.
  have Hnb1 := in_gamma_not_bottom _ _ Hb1.
  have Hnb2 := in_gamma_not_bottom _ _ Hb2.
  rewrite Hkbop //. by apply Hqvop.
Qed.

(** Lift per-bit soundness to Z-level binary_overapproximation. *)
Lemma kb_bitwise_sound
  (zop : Z -> Z -> Z) (bop : bool -> bool -> bool)
  (kbop : must0_must1 -> must0_must1 -> must0_must1)
  (Hzop : forall a b i, testbit (zop a b) i = bop (testbit a i) (testbit b i))
  (Hperbit : forall kb1 kb2 i b1 b2,
    b1 ∈ γ[qv_abs] (kb_testbit kb1 i) ->
    b2 ∈ γ[qv_abs] (kb_testbit kb2 i) ->
    bop b1 b2 ∈ γ[qv_abs] (kb_testbit (kbop kb1 kb2) i))
  : binary_overapproximation kb_ad kb_ad kb_ad kbop (collecting_binary_forward zop).
Proof.
  move=> a2 a1. rewrite /Overapproximates. to_set. unfold_set.
  move=> r [v2 [v1 [Hv2 [Hv1 Hr]]]]. subst. move=> i.
  rewrite Hzop. by apply Hperbit.
Qed.

(** *** Generic bitwise underapproximation *)

(** Given Z-level witness functions whose per-bit values land in gamma,
    we get the underapproximation (completeness) direction. The key
    insight is that γ(kb) is defined pointwise, so per-bit membership
    implies Z-level membership automatically. *)
Lemma kb_bitwise_underapprox
  (zop : Z -> Z -> Z)
  (kbop : must0_must1 -> must0_must1 -> must0_must1)
  (* How to build the witnesses from the picked result and constraints in a2 and a1. *)
  (mk_v2 mk_v1 : Z -> must0_must1 -> must0_must1 -> Z)
  (Hmk_v2 : forall v a2 a1 i,
    v ∈ γ[kb_abs] (kbop a2 a1) -> kb_non_bottom a2 -> kb_non_bottom a1 ->
    testbit (mk_v2 v a2 a1) i ∈ γ[qv_abs] (kb_testbit a2 i))
  (Hmk_v1 : forall v a2 a1 i,
    v ∈ γ[kb_abs] (kbop a2 a1) -> kb_non_bottom a2 -> kb_non_bottom a1 ->
    testbit (mk_v1 v a2 a1) i ∈ γ[qv_abs] (kb_testbit a1 i))
  (Heq : forall v a2 a1,
    v ∈ γ[kb_abs] (kbop a2 a1) -> kb_non_bottom a2 -> kb_non_bottom a1 ->
    zop (mk_v2 v a2 a1) (mk_v1 v a2 a1) = v)
  : forall a2 a1 : nb_must0_must1,
    γ[kb_abs] (kbop (`a2) (`a1)) ⊆
    collecting_binary_forward zop (γ[kb_abs] (`a2)) (γ[kb_abs] (`a1)).
Proof.
  move=> [a2 Hnb2] [a1 Hnb1] v Hv /=.
  unfold_set.
  exists (mk_v2 v a2 a1), (mk_v1 v a2 a1). repeat split.
  - move=> i. exact (Hmk_v2 v a2 a1 i Hv Hnb2 Hnb1).
  - move=> i. exact (Hmk_v1 v a2 a1 i Hv Hnb2 Hnb1).
  - exact (Heq v a2 a1 Hv Hnb2 Hnb1).
Qed.

(** *** Soundness *)
Lemma kb_lor_sound :
  binary_overapproximation kb_ad kb_ad kb_ad kb_lor
    (collecting_binary_forward Z.lor).
Proof.
  apply (kb_bitwise_sound _ orb _ testbit_lor).
  apply (kb_bitwise_perbit_sound _ _ abs_orb kb_testbit_lor).
  move=> q1 q2 b1 b2 Hb1 Hb2.
  apply (abs_orb_exact q1 q2). unfold_set. by exists b1, b2.
Qed.

Lemma kb_land_sound :
  binary_overapproximation kb_ad kb_ad kb_ad kb_land
    (collecting_binary_forward Z.land).
Proof.
  apply (kb_bitwise_sound _ andb _ testbit_land).
  apply (kb_bitwise_perbit_sound _ _ abs_andb kb_testbit_land).
  move=> q1 q2 b1 b2 Hb1 Hb2.
  apply (abs_andb_exact q1 q2). unfold_set. by exists b1, b2.
Qed.

Lemma kb_lxor_sound :
  binary_overapproximation kb_ad kb_ad kb_ad kb_lxor
    (collecting_binary_forward Z.lxor).
Proof.
  apply (kb_bitwise_sound _ xorb _ testbit_lxor).
  apply (kb_bitwise_perbit_sound _ _ abs_xorb kb_testbit_lxor).
  move=> q1 q2 b1 b2 Hb1 Hb2.
  apply (abs_xorb_exact q1 q2). unfold_set. by exists b1, b2.
Qed.

(** *** Non-bottom lift *)

Definition nb_kb_lor : nb_must0_must1 -> nb_must0_must1 -> nb_must0_must1 :=
  NonEmpty.nonempty_lift_total_binary kb_ad kb_non_bottom
    kb_non_bottom_non_empty kb_lor Z.lor (Hsound:=kb_lor_sound).

Definition nb_kb_land : nb_must0_must1 -> nb_must0_must1 -> nb_must0_must1 :=
  NonEmpty.nonempty_lift_total_binary kb_ad kb_non_bottom
    kb_non_bottom_non_empty kb_land Z.land (Hsound:=kb_land_sound).

Definition nb_kb_lxor : nb_must0_must1 -> nb_must0_must1 -> nb_must0_must1 :=
  NonEmpty.nonempty_lift_total_binary kb_ad kb_non_bottom
    kb_non_bottom_non_empty kb_lxor Z.lxor (Hsound:=kb_lxor_sound).

(** *** Exactness *)

(** For lor: witnesses are [v2 = Z.land v (must0 a2)],
    [v1 = Z.land v (must0 a1)]. *)
(** Helper: convert gamma of non-bottom lift result to raw kb gamma. *)
Lemma gamma_nbkb_lor a2 Hnb2 a1 Hnb1 v :
  v ∈ γ[nbkb] (nb_kb_lor (exist _ a2 Hnb2) (exist _ a1 Hnb1)) <->
  v ∈ γ[kb_abs] (kb_lor a2 a1).
Proof. done. Qed.

Lemma gamma_nbkb_land a2 Hnb2 a1 Hnb1 v :
  v ∈ γ[nbkb] (nb_kb_land (exist _ a2 Hnb2) (exist _ a1 Hnb1)) <->
  v ∈ γ[kb_abs] (kb_land a2 a1).
Proof. done. Qed.

Lemma gamma_nbkb_lxor a2 Hnb2 a1 Hnb1 v :
  v ∈ γ[nbkb] (nb_kb_lxor (exist _ a2 Hnb2) (exist _ a1 Hnb1)) <->
  v ∈ γ[kb_abs] (kb_lxor a2 a1).
Proof. done. Qed.
  
(** For lor: witnesses are [v2 = v AND must0(a2)], [v1 = v AND must0(a1)].
    Equation by distributivity and absorption. *)
Lemma kb_lor_exact :
  binary_exact nbkb nbkb nbkb nb_kb_lor
    (collecting_binary_forward Z.lor).
Proof.
  move=> [a2 Hnb2] [a1 Hnb1].
  rewrite /ExactlyRepresents. to_set. split.
  - apply (kb_bitwise_underapprox Z.lor kb_lor
      (fun v a2 _ => Z.land v (must0 a2))
      (fun v _ a1 => Z.land v (must0 a1))).
    + move=> v a2' a1' i Hv Hnb2' Hnb1'. rewrite testbit_land.
      move: (Hv i) (Hnb2' i) (Hnb1' i). rewrite /kb_testbit /kb_lor /=
        !testbit_lor.
      by case_kb2_testbit a2' a1' i;
         unfold_set; destruct (testbit v i).
    + move=> v a2' a1' i Hv Hnb2' Hnb1'. rewrite testbit_land.
      move: (Hv i) (Hnb2' i) (Hnb1' i). rewrite /kb_testbit /kb_lor /=
        !testbit_lor.
      by case_kb2_testbit a2' a1' i;
         unfold_set; destruct (testbit v i).
    + move=> v a2' a1' Hv _ _.
      rewrite -Z.land_lor_distr_r. exact (kb_gamma_land_must0 (kb_lor a2' a1') v Hv).
  - exact (kb_lor_sound a2 a1).
Qed.

(** For land: witnesses are [v2 = v OR must1(a2)], [v1 = v OR must1(a1)].
    Equation by distributivity and absorption. *)
Lemma kb_land_exact :
  binary_exact nbkb nbkb nbkb nb_kb_land
    (collecting_binary_forward Z.land).
Proof.
  move=> [a2 Hnb2] [a1 Hnb1].
  rewrite /ExactlyRepresents. to_set. split.
  - apply (kb_bitwise_underapprox Z.land kb_land
      (fun v a2 _ => Z.lor v (must1 a2))
      (fun v _ a1 => Z.lor v (must1 a1))).
    + move=> v a2' a1' i Hv Hnb2' Hnb1'. rewrite testbit_lor.
      move: (Hv i) (Hnb2' i) (Hnb1' i). rewrite /kb_testbit /kb_land /=
        !testbit_land.
      by case_kb2_testbit a2' a1' i;
         unfold_set; destruct (testbit v i).
    + move=> v a2' a1' i Hv Hnb2' Hnb1'. rewrite testbit_lor.
      move: (Hv i) (Hnb2' i) (Hnb1' i). rewrite /kb_testbit /kb_land /=
        !testbit_land.
      by case_kb2_testbit a2' a1' i;
         unfold_set; destruct (testbit v i).
    + move=> v a2' a1' Hv _ _.
      rewrite -Z.lor_land_distr_r. exact (kb_gamma_lor_must1 (kb_land a2' a1') v Hv).
  - exact (kb_land_sound a2 a1).
Qed.

(** For lxor: witnesses use a mux construction. Where a2 is known,
    [v2] takes the forced value; where a2 is unknown (QTop),
    [v2 = xor(v, must1 a1)] to make [v1] take a1's forced value. *)
Lemma kb_lxor_exact :
  binary_exact nbkb nbkb nbkb nb_kb_lxor
    (collecting_binary_forward Z.lxor).
Proof.
  move=> [a2 Hnb2] [a1 Hnb1].
  rewrite /ExactlyRepresents. to_set. split.
  - set mk_v2 := fun v a2 a1 =>
      let unk2 := Z.lxor (must0 a2) (must1 a2) in
      Z.lor (Z.land (must1 a2) (Z.lnot unk2))
            (Z.land (Z.lxor v (must1 a1)) unk2).
    apply (kb_bitwise_underapprox Z.lxor kb_lxor
      mk_v2 (fun v a2' a1' => Z.lxor v (mk_v2 v a2' a1'))).
    + move=> v a2' a1' i Hv Hnb2' Hnb1'.
      move: (Hv i) (Hnb2' i) (Hnb1' i). rewrite /kb_lxor /kb_testbit /mk_v2 /=.
      autorewrite with bitwise_to_boolean.
      by case_kb2_testbit a2' a1' i;
         unfold_set; destruct (testbit v i).
    + move=> v a2' a1' i Hv Hnb2' Hnb1'.
      move: (Hv i) (Hnb2' i) (Hnb1' i). rewrite /kb_lxor /kb_testbit /mk_v2 /=.
      autorewrite with bitwise_to_boolean.
      by case_kb2_testbit a2' a1' i;
         unfold_set; destruct (testbit v i).
    + move=> v a2' a1' _ _ _. apply Z_testbit_ext => i. rewrite /mk_v2 !testbit_lxor.
      by destruct (testbit (Z.lor _ _) i), (testbit v i).
  - exact (kb_lxor_sound a2 a1).
Qed.

