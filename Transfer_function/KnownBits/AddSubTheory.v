(* AddSubTheory.v - the [Z.add] and [Z.sub] transfer functions ([kb_add],
   [kb_sub]) on the KnownBits single-value abstraction, following
   Vishwanathan et al., CGO 2022 (Listing 1 and §III-B).

   Add and sub are filed together because they share their whole machinery:
   the generic per-bit chain framework ([Section BitChain]: [bit_step],
   [abs_chain], [chain_result_bit] with their generic soundness and
   exactness lemmas), which each instantiates with its own step function
   ([add_step] / [sub_step]), and the Z-level carry sequence [carry_seq],
   which the borrow proofs reduce to ([borrow_carry_witness]).

   Split out of KnownBits.v; the negative precision results at the end
   were previously in AddTheory.v, which this file replaces. *)

(* STATUS:
   add (Z.add): sound + best         (kb_add_sound, kb_add_best)
     NOT γ-exact                     (kb_add_not_exact)
     NOT α-complete                  (kb_add_not_alpha_complete, witness
                                      S1 = {16,20,32,36}, S2 = {16,17})
     Z.add has no exact known-bits abstraction at all
                                     (Zadd_not_exact_on_kb)
   sub (Z.sub): sound + best         (kb_sub_sound, kb_sub_best)
   carry / borrow: sound             (kb_carry_sound, kb_borrow_sound) *)

From Stdlib Require Import ssreflect ssrbool.
Require Import Stdlib.ZArith.ZArith.
From Stdlib Require Import Lia. (* lia/nia; avoid Psatz which loads Reals axioms *)
Require Import base Abstraction AbstractionCombination autoreflect.
Require Import Quadrivalent SvaQuadrivalent KnownBits.
Open Scope Z_scope.

(** *** Non-exactness of integer addition

    The concrete operator [Z.add] does not have an exact known-bits
    abstraction: there is no [kb] whose concretization equals the set of
    pairwise sums [{p+q | p ∈ γ kb1, q ∈ γ kb2}], even for very small
    inputs. Witness: take both inputs to be "bit 0 unknown, other bits
    known 0"; the sum set is {0,1,2}, but any [kb] containing 0, 1, 2 also
    contains 3. *)

(** A one-bit-unknown known-bits value used as witness. *)
Definition kb_one_unknown : must0_must1 := {| must0 := 1; must1 := 0 |}.

Lemma kb_one_unknown_nb : kb_non_bottom kb_one_unknown.
Proof.
  move=> i. rewrite /kb_testbit /kb_one_unknown /must0 /must1 testbit_0.
  by case: (testbit 1 i).
Qed.

Lemma testbit_1_S i : testbit 1 (S i) = false.
Proof.
  rewrite /testbit. apply Z.bits_above_log2; rewrite ?Z.log2_1; lia.
Qed.

Lemma testbit_1_0 : testbit 1 0%nat = true.
Proof. by []. Qed.

Lemma testbit_3_0 : testbit 3 0%nat = true.
Proof. by []. Qed.

Lemma testbit_3_1 : testbit 3 1%nat = true.
Proof. by []. Qed.

Lemma testbit_3_SS i : testbit 3 (S (S i)) = false.
Proof.
  rewrite /testbit. apply Z.bits_above_log2; rewrite ?Z.log2_succ_double; try lia.
  have : (Z.log2 3 = 1)%Z by [].
  lia.
Qed.

Lemma testbit_2_0 : testbit 2 0%nat = false.
Proof. by []. Qed.

Lemma testbit_2_1 : testbit 2 1%nat = true.
Proof. by []. Qed.

Lemma kb_one_unknown_membership v :
  v ∈ γ[kb_abs] kb_one_unknown <-> (v = 0 \/ v = 1).
Proof.
  rewrite kb_gamma_impl. split.
  - move=> H.
    have Hbit_hi : forall i : nat, testbit v (S i) = false.
    { move=> i. have [H0 _] := H (S i). apply H0.
      rewrite /kb_one_unknown /must0. apply testbit_1_S. }
    case Hb0 : (testbit v 0%nat).
    + right. apply Z_testbit_ext => -[|i].
      * by rewrite Hb0 testbit_1_0.
      * by rewrite Hbit_hi testbit_1_S.
    + left. apply Z_testbit_ext => -[|i].
      * by rewrite Hb0 testbit_0.
      * by rewrite Hbit_hi testbit_0.
  - case=> ->; move=> i; rewrite /kb_one_unknown /must0 /must1.
    + split.
      * move=> _. apply testbit_0.
      * by [].
    + split.
      * by [].
      * by rewrite testbit_0.
Qed.

(* MAYBE: redo this proof using α-relations. Given a set S, per bit position i:
   - if every v in S has [testbit v i = false], then [qv_testbit (α S) i = QFalse];
   - if every v in S has [testbit v i = true],  then [qv_testbit (α S) i = QTrue];
   - if S has a v1 with [testbit v1 i = false] and a v2 with [testbit v2 i = true],
     then [qv_testbit (α S) i = QTop].
   The best abstraction of {0,1} + {0,1} = {0,1,2} then also contains 3, so no
   element of the domain concretizes to exactly {0,1,2}. *)
Lemma Zadd_not_exact_on_kb :
  exists kb1 kb2 : must0_must1,
    forall kb : must0_must1,
      γ[kb_abs] kb ⊆⊇ collecting_binary_forward Z.add (γ[kb_abs] kb1) (γ[kb_abs] kb2)
      -> False.
Proof.
  exists kb_one_unknown, kb_one_unknown.
  move=> kb [Hsub Hsup].
  (** Step 1: 0, 1, 2 ∈ γ kb via Hsup. *)
  have G0 : 0 ∈ γ[kb_abs] kb_one_unknown by rewrite kb_one_unknown_membership; tauto.
  have G1 : 1 ∈ γ[kb_abs] kb_one_unknown by rewrite kb_one_unknown_membership; tauto.
  have In_S : forall n, (n = 0 \/ n = 1 \/ n = 2) -> n ∈ collecting_binary_forward Z.add
                (γ[kb_abs] kb_one_unknown) (γ[kb_abs] kb_one_unknown).
  { move=> n Hn. rewrite /collecting_binary_forward. unfold_set.
    case: Hn => [->|[->|->]].
    - by exists 0, 0.
    - by exists 0, 1.
    - by exists 1, 1. }
  have H0 : 0 ∈ γ[kb_abs] kb by apply Hsup, In_S; tauto.
  have H1 : 1 ∈ γ[kb_abs] kb by apply Hsup, In_S; tauto.
  have H2 : 2 ∈ γ[kb_abs] kb by apply Hsup, In_S; tauto.
  (** Step 2: derive that 3 ∈ γ kb. *)
  have H3 : 3 ∈ γ[kb_abs] kb.
  { rewrite kb_gamma_impl => i. split.
    - (** must0 kb i = false → testbit 3 i = false. We show that for i ∈ {0,1},
          must0 kb i is necessarily true, so the implication is vacuous; for
          i ≥ 2, testbit 3 i = false. *)
      case: i => [|[|i]] Hm0.
      + exfalso. have := kb_gamma_must0 kb 1 0%nat H1 Hm0.
        by rewrite testbit_1_0.
      + exfalso. have := kb_gamma_must0 kb 2 1%nat H2 Hm0.
        by rewrite testbit_2_1.
      + apply testbit_3_SS.
    - (** must1 kb i = true → testbit 3 i = true. From 0 ∈ γ kb,
          must1 kb i = true would force testbit 0 i = true, but it's false. *)
      move=> Hm1. exfalso. have := kb_gamma_must1 kb 0 i H0 Hm1.
      by rewrite testbit_0. }
  (** Step 3: 3 ∈ collecting_binary_forward Z.add (γ kb1)(γ kb2) → contradiction. *)
  have H3_in_S := Hsub _ H3.
  have [p [q [Hp [Hq Hsum]]]] : exists p q, p ∈ γ[kb_abs] kb_one_unknown
                                       /\ q ∈ γ[kb_abs] kb_one_unknown
                                       /\ p + q = 3.
  { move: H3_in_S. rewrite /collecting_binary_forward. by unfold_set. }
  rewrite kb_one_unknown_membership in Hp.
  rewrite kb_one_unknown_membership in Hq.
  destruct Hp as [-> | ->]; destruct Hq as [-> | ->]; lia.
Qed.

(** *** kb_add: tnum-style abstract addition (Listing 1 of the paper)

    Translation: the paper's tnum [(P.v, P.m)] maps to our [must1] (=P.v)
    and [unknown_bits] (=P.m). The kernel algorithm is:
        sv := P.v + Q.v
        sm := P.m + Q.m
        Σ  := sv + sm
        χ  := Σ XOR sv
        η  := χ OR P.m OR Q.m
        R.v := sv AND (NOT η)
        R.m := η
    We reconstruct must0 = R.v ∨ R.m so the result is well-formed
    (non-bottom by construction). *)

(** Decomposition: any [p] in [γ kb] splits as [must1 kb + δ], where
    [δ = Z.land p (unknown_bits kb)] has bits only at uncertain positions
    and is bitwise disjoint from [must1 kb]. *)
Lemma kb_decomposition (kb : must0_must1) (p : Z) :
  kb_non_bottom kb -> p ∈ γ[kb_abs] kb ->
  Z.land (must1 kb) (Z.land p (unknown_bits kb)) = 0 /\
  (must1 kb + Z.land p (unknown_bits kb))%Z = p.
Proof.
  move=> Hnb Hp.
  have Hnb' : forall i, ~ (testbit (must0 kb) i = false /\ testbit (must1 kb) i = true).
  { move=> i [Hm0 Hm1]. apply (Hnb i). rewrite /kb_testbit. by rewrite Hm0 Hm1. }
  have Hbits : forall i,
    testbit (must1 kb) i && testbit (Z.land p (unknown_bits kb)) i = false /\
    (testbit (must1 kb) i || testbit (Z.land p (unknown_bits kb)) i) = testbit p i.
  { move=> i.
    rewrite testbit_land /unknown_bits testbit_lxor.
    rewrite kb_gamma_impl in Hp. have [Hi0 Hi1] := Hp i.
    have Hnbi := Hnb' i.
    case Hm0: (testbit (must0 kb) i); case Hm1: (testbit (must1 kb) i);
      case Hpb: (testbit p i) => //=;
      first by have := Hi1 Hm1; rewrite Hpb.
    - by exfalso; apply Hnbi.
    - by exfalso; apply Hnbi.
    - by have := Hi0 Hm0; rewrite Hpb. }
  split.
  - apply Z_testbit_ext => i. rewrite testbit_land testbit_0.
    by have [H _] := Hbits i.
  - have Hand : Z.land (must1 kb) (Z.land p (unknown_bits kb)) = 0.
    { apply Z_testbit_ext => i. rewrite testbit_land testbit_0.
      by have [H _] := Hbits i. }
    have Hor : Z.lor (must1 kb) (Z.land p (unknown_bits kb)) = p.
    { apply Z_testbit_ext => i. rewrite testbit_lor.
      by have [_ H] := Hbits i. }
    have := Z.add_lor_land (must1 kb) (Z.land p (unknown_bits kb)).
    by rewrite Hor Hand; lia.
Qed.

(** *** Closed-form [kb_add] — Vishwanathan et al., Listing 1, p.258.

    The kernel's [tnum_add] in σ-decomposed form: combine value sums
    and mask sums into a single carry expression, and read off the
    result tnum. The variable naming (sv, sm, sigma, chi, eta, rv)
    matches the paper exactly. *)
Definition kb_add (kb1 kb2 : must0_must1) : must0_must1 :=
  let v1    := must1 kb1 in
  let m1    := unknown_bits kb1 in
  let v2    := must1 kb2 in
  let m2    := unknown_bits kb2 in
  let sv    := (v1 + v2)%Z in
  let sm    := (m1 + m2)%Z in
  let sigma := (sv + sm)%Z in
  let chi   := Z.lxor sigma sv in
  let eta   := Z.lor chi (Z.lor m1 m2) in
  let rv    := Z.land sv (Z.lnot eta) in
  {| must1 := rv;
     must0 := Z.lor rv eta |}.

(** *** Generic per-bit chain framework

    Both addition (carry) and subtraction (borrow) follow the same
    per-bit recurrence pattern:

      chain[0] = init (e.g. QFalse for carry/borrow)
      chain[i+1] = step(p[i], q[i], chain[i])

    where [step] is a quadrivalent operator that abstracts a concrete
    boolean function [f : bool → bool → bool → bool].

    The framework below captures this shared structure once, with
    generic soundness and joint-exactness lemmas parameterized by
    [step], [f], and the Z-level chain sequence. Each operator (+, −,
    later shifts-with-carry, ...) instantiates [step] and [f] and
    provides the Z-level chain recurrence; the induction skeleton is
    reused without duplication.

    Vishwanathan et al. (§III-B) remark that subtraction is proved
    "very similar in structure" to addition but only present the
    addition proof in the main body, leaving subtraction to the
    extended technical report.  The chain framework here makes the
    similarity literal in Rocq: the [step_sound] / [step_realize] /
    [abs_chain_sound] / [abs_chain_joint_exact] /
    [chain_result_bit_exact] lemmas are proven once and instantiated
    twice (for [add_step]/[add_bit] and [sub_step]/[sub_bit]). *)

(** Pick the right [(a, b, d) ∈ bool³] witness from the 8 possibilities.
    Shared between [add_step_realize] and [sub_step_realize] (defined
    below) since they differ only in the concrete bit function. Lives
    above [Section BitChain] so it remains visible to [sub_step_realize]
    which is outside that section. *)
Ltac realize_step_witness :=
  first
    [ exists false, false, false; by unfold_set
    | exists false, false, true;  by unfold_set
    | exists false, true,  false; by unfold_set
    | exists false, true,  true;  by unfold_set
    | exists true,  false, false; by unfold_set
    | exists true,  false, true;  by unfold_set
    | exists true,  true,  false; by unfold_set
    | exists true,  true,  true;  by unfold_set ].

Section BitChain.

(** Per-bit abstract transition: from abstract bits of (p[i], q[i], prev-chain[i])
    produce the next chain bit. *)
Definition bit_step : Type :=
  quadrivalent -> quadrivalent -> quadrivalent -> quadrivalent.

(** Concrete boolean function that [bit_step] abstracts. *)
Definition bit_step_concrete : Type := bool -> bool -> bool -> bool.

(** [step_sound step f]: [f] is a sound concretization of [step]. *)
Definition step_sound (step : bit_step) (f : bit_step_concrete) : Prop :=
  forall x y z a b c,
    a ∈ γ[qv_abs] x -> b ∈ γ[qv_abs] y -> c ∈ γ[qv_abs] z ->
    f a b c ∈ γ[qv_abs] (step x y z).

(** [step_realize step f]: every abstract output of [step] is realized by
    some triple of concrete inputs drawn from the γ-sets of the arguments. *)
Definition step_realize (step : bit_step) (f : bit_step_concrete) : Prop :=
  forall x y z c,
    c ∈ γ[qv_abs] (step x y z) ->
    exists a b d,
      a ∈ γ[qv_abs] x /\ b ∈ γ[qv_abs] y /\ d ∈ γ[qv_abs] z /\
      c = f a b d.

(** Generic recursive abstract chain. *)
Fixpoint abs_chain (step : bit_step) (init : quadrivalent)
                   (kb1 kb2 : must0_must1) (i : nat) : quadrivalent :=
  match i with
  | 0%nat   => init
  | S i'    => step (kb_testbit kb1 i') (kb_testbit kb2 i')
                    (abs_chain step init kb1 kb2 i')
  end.

(** Generic per-bit abstract result of a binary Z operation:
    [result[i] = p[i] ⊕ q[i] ⊕ chain[i]]. *)
Definition chain_result_bit (step : bit_step) (init : quadrivalent)
                            (kb1 kb2 : must0_must1) (i : nat) : quadrivalent :=
  abs_xorb (abs_xorb (kb_testbit kb1 i) (kb_testbit kb2 i))
           (abs_chain step init kb1 kb2 i).

(** ** Instance: addition (carry chain)

    The carry recurrence:

      c[0] = 0
      c[i+1] = (p[i] & q[i]) | (c[i] & (p[i] | q[i]))

    Abstracted by [add_step] (majority-of-three on abstract bits). *)

Definition add_step : bit_step :=
  fun x y z => abs_orb (abs_andb x y) (abs_andb z (abs_orb x y)).

Definition add_bit : bit_step_concrete :=
  fun a b c => (a && b) || (c && (a || b)).

Lemma add_step_sound : step_sound add_step add_bit.
Proof.
  move=> x y z a b c Ha Hb Hc.
  rewrite /add_step /add_bit.
  apply (abs_orb_exact _ _). unfold_set.
  exists (a && b), (c && (a || b)).
  repeat split.
  - apply (abs_andb_exact _ _). unfold_set. by exists a, b.
  - apply (abs_andb_exact _ _). unfold_set.
    exists c, (a || b). repeat split=> //.
    apply (abs_orb_exact _ _). unfold_set. by exists a, b.
Qed.

Lemma add_step_realize : step_realize add_step add_bit.
Proof.
  move=> x y z c. rewrite /add_step /add_bit.
  by destruct x, y, z, c; unfold_set => H; try done; realize_step_witness.
Qed.

End BitChain.

(** Subtraction borrow at the concrete bit level:
    [borrow[i+1] = (¬p[i] ∧ q[i]) ∨ (borrow[i] ∧ (¬p[i] ∨ q[i]))]. *)
Definition sub_bit : bit_step_concrete :=
  fun a b c => (negb a && b) || (c && (negb a || b)).

(** Bind [abs_carry] and [result_bit] to the generic chain with [add_step]. *)
Definition abs_carry := abs_chain add_step QFalse.
Definition result_bit := chain_result_bit add_step QFalse.

(** Per-bit abstract carry and result_bit are defined above as instances
    of the generic [abs_chain] / [chain_result_bit] framework. *)

(** *** Soundness of the abstract carry

    For any [p ∈ γ kb1], [q ∈ γ kb2], the concrete carry bit at position [i]
    of [p + q] lands in [γ_qv (abs_carry kb1 kb2 i)]. We extract the
    concrete carry sequence from [Z.add_carry_bits]. *)

(** Witness existence of the concrete carry sequence for [p + q].
    Paper: Definition 1 (full-adder equations) — [c_out[i]] is exactly
    the [c] this lemma exhibits. *)
Lemma concrete_carry_seq (p q : Z) :
  exists c : Z,
    Z.testbit c 0 = false /\
    (forall i : nat,
      Z.testbit c (Z.of_nat (S i)) =
        (testbit p i && testbit q i) || (Z.testbit c (Z.of_nat i) && (testbit p i || testbit q i)))
    /\ (forall i : nat,
      testbit (p + q) i = xorb (xorb (testbit p i) (testbit q i)) (Z.testbit c (Z.of_nat i))).
Proof.
  have [c [Hsum [Hrec Hc0]]] := Z.add_carry_bits p q false.
  rewrite /= Z.add_0_r in Hsum.
  exists c. split; [|split].
  - exact Hc0.
  - move=> i. rewrite Nat2Z.inj_succ -Z.add_1_r.
    have Hge : (0 <= Z.of_nat i)%Z by lia.
    have := f_equal (fun z => Z.testbit z (Z.of_nat i)) Hrec.
    rewrite Z.div2_bits // -Z.add_1_r.
    rewrite Z.lor_spec !Z.land_spec Z.lor_spec.
    move=> ->. by rewrite -/(testbit p i) -/(testbit q i).
  - move=> i. rewrite /testbit Hsum.
    rewrite !Z.lxor_spec.
    by rewrite -/(testbit p i) -/(testbit q i).
Qed.

(** ** Generic soundness of [abs_chain].

    For any chain recurrence satisfying [step_sound], the abstract chain
    over-approximates the concrete chain at every bit position. *)
Lemma abs_chain_sound
  (step : bit_step) (f : bit_step_concrete) (init : quadrivalent) (init_b : bool)
  (Hstep : step_sound step f)
  (Hinit : init_b ∈ γ[qv_abs] init)
  (kb1 kb2 : must0_must1) (p q : Z)
  (Hp : p ∈ γ[kb_abs] kb1) (Hq : q ∈ γ[kb_abs] kb2)
  (c : Z)
  (Hc0   : Z.testbit c 0 = init_b)
  (Hcrec : forall j : nat,
      Z.testbit c (Z.of_nat (S j)) =
        f (testbit p j) (testbit q j) (Z.testbit c (Z.of_nat j)))
  : forall i, Z.testbit c (Z.of_nat i) ∈ γ[qv_abs] (abs_chain step init kb1 kb2 i).
Proof.
  have Hp' : forall i, testbit p i ∈ γ[qv_abs] (kb_testbit kb1 i)
    by move=> j; exact (Hp j).
  have Hq' : forall i, testbit q i ∈ γ[qv_abs] (kb_testbit kb2 i)
    by move=> j; exact (Hq j).
  move=> i.
  elim: i => [|i IH].
  - rewrite /abs_chain Nat2Z.inj_0 Hc0. exact Hinit.
  - rewrite /abs_chain. rewrite (Hcrec i).
    exact: Hstep (Hp' i) (Hq' i) IH.
Qed.

(** Soundness of [abs_carry]: at every bit, the concrete carry lies in the
    abstract carry's concretization, for any choice of [(p, q) ∈ γ kb1 × γ kb2].
    Paper: Lemma 2 (Minimum carries) — every concrete carry that can
    arise is in the abstract carry's γ. *)
Lemma abs_carry_sound (kb1 kb2 : must0_must1) (p q : Z) :
  p ∈ γ[kb_abs] kb1 -> q ∈ γ[kb_abs] kb2 ->
  forall i c,
    Z.testbit c 0 = false ->
    (forall j : nat,
      Z.testbit c (Z.of_nat (S j)) =
        (testbit p j && testbit q j) || (Z.testbit c (Z.of_nat j) && (testbit p j || testbit q j))) ->
    Z.testbit c (Z.of_nat i) ∈ γ[qv_abs] (abs_carry kb1 kb2 i).
Proof.
  move=> Hp Hq i c Hc0 Hrec.
  have Hinit : false ∈ γ[qv_abs] QFalse by unfold_set.
  exact: abs_chain_sound add_step add_bit QFalse false
    add_step_sound Hinit kb1 kb2 p q Hp Hq c Hc0 Hrec i.
Qed.

(** ** Generic soundness of [chain_result_bit].

    Given the Z-level bit identity [testbit (op p q) i = p[i] ⊕ q[i] ⊕ chain p q [i]]
    and the chain recurrence, the abstract per-bit result over-approximates
    the concrete result. *)
Lemma chain_result_bit_sound
  (step : bit_step) (f : bit_step_concrete)
  (init : quadrivalent) (init_b : bool)
  (Hstep  : step_sound step f)
  (Hinit  : init_b ∈ γ[qv_abs] init)
  (op chain : Z -> Z -> Z)
  (Hbit : forall p q i,
      testbit (op p q) i =
        xorb (xorb (testbit p i) (testbit q i)) (testbit (chain p q) i))
  (Hchain0   : forall p q, testbit (chain p q) 0 = init_b)
  (Hchainrec : forall p q j,
      testbit (chain p q) (S j) =
        f (testbit p j) (testbit q j) (testbit (chain p q) j))
  (kb1 kb2 : must0_must1) (p q : Z) :
  p ∈ γ[kb_abs] kb1 -> q ∈ γ[kb_abs] kb2 ->
  forall i, testbit (op p q) i ∈ γ[qv_abs] (chain_result_bit step init kb1 kb2 i).
Proof.
  move=> Hp Hq i.
  have Hp' : forall j, testbit p j ∈ γ[qv_abs] (kb_testbit kb1 j)
    by move=> j; exact (Hp j).
  have Hq' : forall j, testbit q j ∈ γ[qv_abs] (kb_testbit kb2 j)
    by move=> j; exact (Hq j).
  rewrite Hbit. rewrite /chain_result_bit.
  apply (abs_xorb_exact _ _). unfold_set.
  exists (xorb (testbit p i) (testbit q i)), (testbit (chain p q) i).
  repeat split.
  - apply (abs_xorb_exact _ _). unfold_set. exists (testbit p i), (testbit q i).
    by repeat split.
  - apply: abs_chain_sound step f init init_b Hstep Hinit
      kb1 kb2 p q Hp Hq (chain p q) (Hchain0 p q) (Hchainrec p q) i.
Qed.

(** Soundness of [result_bit] over [Z.add].
    Paper: Lemma 2 specialised to the result bit (carry + XOR). *)
Lemma result_bit_sound (kb1 kb2 : must0_must1) (p q : Z) :
  p ∈ γ[kb_abs] kb1 -> q ∈ γ[kb_abs] kb2 ->
  forall i, testbit (p + q) i ∈ γ[qv_abs] (result_bit kb1 kb2 i).
Proof.
  move=> Hp Hq i.
  have Hp' : forall j, testbit p j ∈ γ[qv_abs] (kb_testbit kb1 j)
    by move=> j; exact (Hp j).
  have Hq' : forall j, testbit q j ∈ γ[qv_abs] (kb_testbit kb2 j)
    by move=> j; exact (Hq j).
  have [c [Hc0 [Hrec Hsum]]] := concrete_carry_seq p q.
  rewrite Hsum. rewrite /result_bit /chain_result_bit.
  apply (abs_xorb_exact _ _). unfold_set.
  exists (xorb (testbit p i) (testbit q i)), (Z.testbit c (Z.of_nat i)).
  repeat split.
  - apply (abs_xorb_exact _ _). unfold_set. exists (testbit p i), (testbit q i).
    by repeat split.
  - exact: abs_carry_sound kb1 kb2 p q Hp Hq i c Hc0 Hrec.
Qed.

(** *** Z-level abstract carry [kb_carry]

    The concrete carry sequence of [p + q] is the [Z] with bit [i]
    holding the carry into bit [i]:
        [carry_seq p q = Z.lxor (Z.lxor (p + q) p) q].
    Its bit at [i] is 0 for [i = 0], and otherwise equals the standard
    full-adder recurrence. We abstract it by a [must0_must1] whose
    [must1] is the carry-of-[v1+v2] (the minimum carries) and whose
    [must0] is the carry-of-(must0 kb1 + must0 kb2) (the maximum carries,
    since [must0 = v + m] is the bit pattern with all uncertain bits set
    to 1). *)

Definition carry_seq (p q : Z) : Z := Z.lxor (Z.lxor (p + q) p) q.

Definition kb_carry (kb1 kb2 : must0_must1) : must0_must1 :=
  {| must1 := carry_seq (must1 kb1) (must1 kb2);
     must0 := carry_seq (must0 kb1) (must0 kb2) |}.

(** Carry recurrence at the Z level. *)
Lemma testbit_carry_seq_0 (x y : Z) : testbit (carry_seq x y) 0%nat = false.
Proof.
  rewrite /carry_seq /=. rewrite /testbit.
  rewrite !Z.lxor_spec.
  rewrite Z.add_bit0. by case: (Z.testbit x 0); case: (Z.testbit y 0).
Qed.

Lemma testbit_carry_seq_succ (x y : Z) (j : nat) :
  testbit (carry_seq x y) (S j) =
    (testbit x j && testbit y j)
    || (testbit (carry_seq x y) j && (testbit x j || testbit y j)).
Proof.
  have [c [Hsum [Hrec Hc0]]] := Z.add_carry_bits x y false.
  rewrite /= Z.add_0_r in Hsum.
  (** carry_seq x y = c, by lxor manipulation. *)
  have Hcs : carry_seq x y = c.
  { rewrite /carry_seq Hsum. apply Z.bits_inj' => n Hn.
    rewrite !Z.lxor_spec.
    by case: (Z.testbit x n); case: (Z.testbit y n); case: (Z.testbit c n). }
  rewrite Hcs.
  rewrite /testbit Nat2Z.inj_succ -Z.add_1_r.
  have Hge : (0 <= Z.of_nat j)%Z by lia.
  have := f_equal (fun z => Z.testbit z (Z.of_nat j)) Hrec.
  rewrite Z.div2_bits // -Z.add_1_r => ->.
  rewrite Z.lor_spec !Z.land_spec Z.lor_spec.
  by rewrite -/(testbit x j) -/(testbit y j).
Qed.

Hint Rewrite @testbit_carry_seq_0 @testbit_carry_seq_succ : bitwise_to_boolean.

(** Per-bit equivalence between the Z-level [kb_carry] and the recursive
    [abs_carry]. *)
Lemma kb_testbit_kb_carry (kb1 kb2 : must0_must1) (i : nat) :
  kb_non_bottom kb1 -> kb_non_bottom kb2 ->
  kb_testbit (kb_carry kb1 kb2) i = abs_carry kb1 kb2 i.
Proof.
  move=> HNB1 HNB2.
  rewrite /abs_carry.
  elim: i => [|i IH].
  - rewrite /kb_testbit /kb_carry /must0 /must1.
    by rewrite !testbit_carry_seq_0.
  - rewrite /kb_testbit /kb_carry /=.
    rewrite !testbit_carry_seq_succ.
    rewrite -IH.
    apply /qv_eqbP.
    move: (HNB1 i) (HNB2 i). rewrite /kb_testbit.
    have [p Hp] := proj1 (kb_non_bottom_non_empty kb1) HNB1.
    have [q Hq] := proj1 (kb_non_bottom_non_empty kb2) HNB2.
    have [c [Hc0 [Hrec _]]] := concrete_carry_seq p q.
    have CNB : abs_chain add_step QFalse kb1 kb2 i <> QBottom
      := in_gamma_not_bottom _ _ (abs_carry_sound kb1 kb2 p q Hp Hq i c Hc0 Hrec).
    move: CNB. rewrite -IH /kb_testbit /kb_carry /=.
    case_kb2_testbit kb1 kb2 i;
    case_testbits i (carry_seq (must0 kb1) (must0 kb2))
                    (carry_seq (must1 kb1) (must1 kb2)) => //=;
    try discriminate; try tauto; reflexivity.
Qed.

(** [kb_carry] is a sound binary overapproximation of [carry_seq]:
    for any [p ∈ γ kb1, q ∈ γ kb2], the concrete carry sequence
    [carry_seq p q] is in [γ (kb_carry kb1 kb2)]. *)
Lemma kb_carry_sound :
  binary_overapproximation kb_ad kb_ad kb_ad kb_carry
    (collecting_binary_forward carry_seq).
Proof.
  move=> kb2 kb1 v Hv. unfold_set in Hv.
  destruct Hv as [p [q [Hp [Hq Hv]]]]. subst.
  have Hnb2 : kb_non_bottom kb2 by apply kb_non_bottom_non_empty; exists p.
  have Hnb1 : kb_non_bottom kb1 by apply kb_non_bottom_non_empty; exists q.
  unfold_set => i. rewrite kb_testbit_kb_carry //.
  exact: (abs_carry_sound kb2 kb1 p q Hp Hq i (carry_seq p q)
           (testbit_carry_seq_0 p q) (testbit_carry_seq_succ p q)).
Qed.

(** ** Constructive exactness of [abs_carry] and [result_bit]

    We prove the per-bit exactness of [abs_carry] (joint with the
    input bits) and then of [result_bit]. The argument is constructive
    and goes by induction on the bit position. *)

(** Generalization of [kb_gamma_set_free_bit]: bit [i] of [v ∈ γ kb]
    can be replaced by any [b ∈ γ_qv (kb_testbit kb i)] and the result
    stays in [γ kb]. *)
Lemma kb_gamma_setbit (kb : must0_must1) (v : Z) (i : nat) (b : bool) :
  v ∈ γ[kb_abs] kb ->
  b ∈ γ[qv_abs] (kb_testbit kb i) ->
  setbit_to v i b ∈ γ[kb_abs] kb.
Proof.
  move=> Hv Hb j. unfold_set.
  case (Nat.eq_dec i j) => [<- | Hneq].
  - by rewrite testbit_over_setbit_same; move: Hb; unfold_set.
  - rewrite testbit_over_setbit_different //. by have := (Hv j); unfold_set.
Qed.

(** Locality of the carry sequence: bit [i] of [carry_seq p q] only
    depends on bits strictly below [i] of [p] and [q]. *)
Lemma testbit_carry_seq_low_invariant (p q p' q' : Z) (i : nat) :
  (forall j, (j < i)%nat -> testbit p j = testbit p' j) ->
  (forall j, (j < i)%nat -> testbit q j = testbit q' j) ->
  testbit (carry_seq p q) i = testbit (carry_seq p' q') i.
Proof.
  elim: i => [|i IH] Hp Hq.
  - by rewrite !testbit_carry_seq_0.
  - rewrite !testbit_carry_seq_succ.
    have Hpi : testbit p i = testbit p' i by apply Hp; lia.
    have Hqi : testbit q i = testbit q' i by apply Hq; lia.
    rewrite Hpi Hqi.
    rewrite (IH _ _) //; move=> j Hj; [apply Hp | apply Hq]; lia.
Qed.

(** Bit-level full-adder identity: [testbit (p+q) i] is the xor of the
    input bits and the carry bit.
    Paper: Definition 1 — [r[i] = p[i] ⊕ q[i] ⊕ c_in[i]]. *)
Lemma testbit_add_xor_carry (p q : Z) (i : nat) :
  testbit (p + q) i =
  xorb (xorb (testbit p i) (testbit q i)) (testbit (carry_seq p q) i).
Proof.
  rewrite /carry_seq /testbit !Z.lxor_spec.
  by case: (Z.testbit p _); case: (Z.testbit q _); case: (Z.testbit (p+q) _).
Qed.

(** *** Borrow sequence for subtraction

    Mirror of the carry-sequence infrastructure for [p - q]. *)

Definition borrow_seq (p q : Z) : Z := Z.lxor (Z.lxor (p - q) p) q.

(** Bit-level full-subtractor identity: [testbit (p-q) i] is the xor of the
    input bits and the borrow bit. Purely lxor algebra on [borrow_seq].
    Paper: full-subtractor analog of Definition 1 (sketched §III-B). *)
Lemma testbit_sub_xor_borrow (p q : Z) (i : nat) :
  testbit (p - q) i =
  xorb (xorb (testbit p i) (testbit q i)) (testbit (borrow_seq p q) i).
Proof.
  rewrite /borrow_seq /testbit !Z.lxor_spec.
  by case: (Z.testbit p _); case: (Z.testbit q _); case: (Z.testbit (p - q) _).
Qed.

(** Single witness for [borrow_seq]: the carry sequence [c] of
    [Z.add_carry_bits x (Z.lnot y) true] (which realises [x - y] via
    [Z.succ_add_lnot_r]) satisfies [borrow_seq x y = Z.lnot c]. All three
    borrow lemmas below ([_0], [_succ], [concrete_]) reuse this witness
    rather than re-deriving the [Z.lnot c] identity. *)
Local Lemma borrow_carry_witness (x y : Z) :
  exists c : Z,
    borrow_seq x y = Z.lnot c /\
    Z.testbit c 0 = true /\
    (forall j : nat,
      Z.testbit c (Z.of_nat (S j)) =
        (testbit x j && testbit (Z.lnot y) j)
        || (Z.testbit c (Z.of_nat j) && (testbit x j || testbit (Z.lnot y) j))).
Proof.
  have [c [Hsum [Hrec Hc0]]] := Z.add_carry_bits x (Z.lnot y) true.
  rewrite Z.succ_add_lnot_r in Hsum.
  exists c. split; [|split].
  - rewrite /borrow_seq Hsum.
    apply Z.bits_inj' => n Hn.
    rewrite !Z.lxor_spec !(Z.lnot_spec _ _ Hn).
    by case: (Z.testbit x n); case: (Z.testbit y n); case: (Z.testbit c n).
  - exact Hc0.
  - move=> j. rewrite Nat2Z.inj_succ -Z.add_1_r.
    have Hge : (0 <= Z.of_nat j)%Z by lia.
    have := f_equal (fun z => Z.testbit z (Z.of_nat j)) Hrec.
    rewrite Z.div2_bits // -Z.add_1_r.
    rewrite Z.lor_spec !Z.land_spec Z.lor_spec.
    by move=> ->.
Qed.

(** Borrow recurrence at the Z level. *)
Lemma testbit_borrow_seq_0 (x y : Z) : testbit (borrow_seq x y) 0%nat = false.
Proof.
  have [c [Hbs [Hc0 _]]] := borrow_carry_witness x y.
  by rewrite Hbs /testbit (Z.lnot_spec c 0 ltac:(lia)) Hc0.
Qed.

Lemma testbit_borrow_seq_succ (x y : Z) (j : nat) :
  testbit (borrow_seq x y) (S j) =
    (negb (testbit x j) && testbit y j)
    || (testbit (borrow_seq x y) j && (negb (testbit x j) || testbit y j)).
Proof.
  have [c [Hbs [_ Hrec]]] := borrow_carry_witness x y.
  rewrite Hbs /testbit.
  have Hpos_j  : (0 <= Z.of_nat j)%Z      by lia.
  have Hpos_sj : (0 <= Z.of_nat (S j))%Z  by lia.
  rewrite (Z.lnot_spec c (Z.of_nat (S j)) Hpos_sj)
          (Z.lnot_spec c (Z.of_nat j) Hpos_j).
  rewrite (Hrec j) testbit_lnot.
  rewrite -/(testbit x j) -/(testbit y j).
  by case: (testbit x j); case: (testbit y j); case: (Z.testbit c (Z.of_nat j)).
Qed.

(** Locality of the borrow sequence: bit [i] of [borrow_seq p q] only
    depends on bits strictly below [i] of [p] and [q]. *)
Lemma testbit_borrow_seq_low_invariant (p q p' q' : Z) (i : nat) :
  (forall j, (j < i)%nat -> testbit p j = testbit p' j) ->
  (forall j, (j < i)%nat -> testbit q j = testbit q' j) ->
  testbit (borrow_seq p q) i = testbit (borrow_seq p' q') i.
Proof.
  elim: i => [|i IH] Hp Hq.
  - by rewrite !testbit_borrow_seq_0.
  - rewrite !testbit_borrow_seq_succ.
    have Hpi : testbit p i = testbit p' i by apply Hp; lia.
    have Hqi : testbit q i = testbit q' i by apply Hq; lia.
    rewrite Hpi Hqi.
    rewrite (IH _ _) //; move=> j Hj; [apply Hp | apply Hq]; lia.
Qed.

(** Witness existence of the concrete borrow sequence for [p - q]:
    composes the three primitive borrow lemmas above.
    Paper: full-subtractor analog of Definition 1 (the borrow [b]
    plays the role of the carry [c] in §III-B's subtraction sketch). *)
Lemma concrete_borrow_seq (p q : Z) :
  exists b : Z,
    Z.testbit b 0 = false /\
    (forall i : nat,
      Z.testbit b (Z.of_nat (S i)) =
        (negb (testbit p i) && testbit q i)
        || (Z.testbit b (Z.of_nat i) && (negb (testbit p i) || testbit q i)))
    /\ (forall i : nat,
      testbit (p - q) i =
        xorb (xorb (testbit p i) (testbit q i)) (Z.testbit b (Z.of_nat i))).
Proof.
  exists (borrow_seq p q); split; [|split].
  - exact: testbit_borrow_seq_0.
  - exact: testbit_borrow_seq_succ.
  - exact: testbit_sub_xor_borrow.
Qed.

(** *** Abstract subtraction borrow step

    [sub_step] abstracts the borrow recurrence over quadrivalent values. *)

Definition sub_step : bit_step :=
  fun x y z => abs_orb (abs_andb (abs_negb x) y) (abs_andb z (abs_orb (abs_negb x) y)).

Lemma sub_step_sound : step_sound sub_step sub_bit.
Proof.
  move=> x y z a b c Ha Hb Hc.
  rewrite /sub_step /sub_bit.
  apply (abs_orb_exact _ _). unfold_set.
  exists (negb a && b), (c && (negb a || b)). split; [|split].
  - apply (abs_andb_exact _ _). unfold_set.
    exists (negb a), b. split; [|split].
    + apply (abs_negb_exact x). unfold_set. exists a; split; [exact Ha|reflexivity].
    + exact Hb.
    + reflexivity.
  - apply (abs_andb_exact _ _). unfold_set.
    exists c, (negb a || b). split; [|split].
    + exact Hc.
    + apply (abs_orb_exact _ _). unfold_set.
      exists (negb a), b. split; [|split].
      * apply (abs_negb_exact x). unfold_set. exists a; split; [exact Ha|reflexivity].
      * exact Hb.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma sub_step_realize : step_realize sub_step sub_bit.
Proof.
  move=> x y z c. rewrite /sub_step /sub_bit.
  by destruct x, y, z, c; unfold_set => H; try done; realize_step_witness.
Qed.

(** Per-bit abstract borrow and result for subtraction, instantiated from
    the generic chain framework. *)
Definition abs_borrow := abs_chain sub_step QFalse.
Definition result_bit_sub := chain_result_bit sub_step QFalse.

(** Step lemma: every bit in the abstract carry's gamma is realized
    as the majority of three concrete bits drawn from the gammas of
    the three input quadrivalents. The proof is by exhaustive case
    analysis on [(x, y, z, c)]. *)
Lemma abs_carry_step_realize (x y z : quadrivalent) (c : bool) :
  c ∈ γ[qv_abs] (abs_orb (abs_andb x y) (abs_andb z (abs_orb x y))) ->
  exists a b d,
    a ∈ γ[qv_abs] x /\ b ∈ γ[qv_abs] y /\ d ∈ γ[qv_abs] z /\
    c = (a && b) || (d && (a || b)).
Proof. exact: add_step_realize. Qed.

(** ** Generic joint exactness of [abs_chain].

    For any [(b1, b2, c)] in the product γ-set at position [i],
    there exist [(p, q)] in [γ a1 × γ a2] realizing them at bit [i],
    including the chain bit. *)
Lemma abs_chain_joint_exact
  (step : bit_step) (f : bit_step_concrete)
  (init : quadrivalent) (init_b : bool)
  (Hreal : step_realize step f)
  (Hinit_only : forall c, c ∈ γ[qv_abs] init -> c = init_b)
  (chain : Z -> Z -> Z)
  (Hchain0    : forall p q, testbit (chain p q) 0 = init_b)
  (Hchainrec  : forall p q j,
      testbit (chain p q) (S j) =
        f (testbit p j) (testbit q j) (testbit (chain p q) j))
  (Hchainlow  : forall p q p' q' i,
      (forall j, (j < i)%nat -> testbit p j = testbit p' j) ->
      (forall j, (j < i)%nat -> testbit q j = testbit q' j) ->
      testbit (chain p q) i = testbit (chain p' q') i)
  (a1 a2 : nb_must0_must1) (i : nat) (b1 b2 c : bool) :
  b1 ∈ γ[qv_abs] (kb_testbit (`a1) i) ->
  b2 ∈ γ[qv_abs] (kb_testbit (`a2) i) ->
  c  ∈ γ[qv_abs] (abs_chain step init (`a1) (`a2) i) ->
  exists p q,
    p ∈ γ[kb_abs] (`a1) /\ q ∈ γ[kb_abs] (`a2) /\
    testbit p i = b1 /\ testbit q i = b2 /\
    testbit (chain p q) i = c.
Proof.
  move: a1 a2 => [a1 Hnb1] [a2 Hnb2] /=.
  elim: i b1 b2 c => [|i IH] b1 b2 c Hb1 Hb2 Hc.
  - (** i = 0: c is forced to init_b by Hinit_only; pick witnesses
        via kb_testbit_exact. *)
    rewrite /abs_chain in Hc.
    move: (Hinit_only _ Hc) => ->.
    have [Hsub1 _] := kb_testbit_exact (exist _ a1 Hnb1) 0%nat.
    have [Hsub2 _] := kb_testbit_exact (exist _ a2 Hnb2) 0%nat.
    have := Hsub1 b1 Hb1. unfold_set => [[p [Hp Hpb]]].
    have := Hsub2 b2 Hb2. unfold_set => [[q [Hq Hqb]]].
    exists p, q; repeat split; [exact Hp|exact Hq|exact Hpb|exact Hqb|apply Hchain0].
  - (** i = S i': use Hreal + IH at i', then overwrite bit (S i). *)
    rewrite /abs_chain in Hc. simpl in Hc.
    have [a [b_ [d [Ha [Hb [Hd Hf]]]]]] := Hreal _ _ _ _ Hc.
    have [p_low [q_low [Hp_low [Hq_low [Hpi [Hqi Hci]]]]]] :=
      IH a b_ d Ha Hb Hd.
    set p := setbit_to p_low (S i) b1.
    set q := setbit_to q_low (S i) b2.
    exists p, q. repeat split.
    + exact: (kb_gamma_setbit a1 p_low (S i) b1 Hp_low Hb1).
    + exact: (kb_gamma_setbit a2 q_low (S i) b2 Hq_low Hb2).
    + exact: testbit_over_setbit_same.
    + exact: testbit_over_setbit_same.
    + rewrite Hchainrec Hf.
      have Hpi' : testbit p i = testbit p_low i
        by apply testbit_over_setbit_different; lia.
      have Hqi' : testbit q i = testbit q_low i
        by apply testbit_over_setbit_different; lia.
      have Hcsi : testbit (chain p q) i = testbit (chain p_low q_low) i.
      { apply Hchainlow; move=> j Hj;
          apply testbit_over_setbit_different; lia. }
      by rewrite Hpi' Hqi' Hcsi Hpi Hqi Hci.
Qed.

(** Joint constructive exactness of [abs_carry]. For any [(b1, b2, c)]
    in the product γ-set at position [i], there exist [(p, q)] in
    [γ a1 × γ a2] realizing them at bit [i], including the carry.
    Paper: Lemma 4 (Capture uncertainty) + Eqn 6 (bitwise-exact α). *)
Lemma abs_carry_joint_exact (a1 a2 : nb_must0_must1) (i : nat) (b1 b2 c : bool) :
  b1 ∈ γ[qv_abs] (kb_testbit (`a1) i) ->
  b2 ∈ γ[qv_abs] (kb_testbit (`a2) i) ->
  c ∈ γ[qv_abs] (abs_carry (`a1) (`a2) i) ->
  exists p q,
    p ∈ γ[kb_abs] (`a1) /\ q ∈ γ[kb_abs] (`a2) /\
    testbit p i = b1 /\ testbit q i = b2 /\
    testbit (carry_seq p q) i = c.
Proof.
  move=> Hb1 Hb2 Hc.
  have Hinit_only : forall c', c' ∈ γ[qv_abs] QFalse -> c' = false.
  { move=> c'. unfold_set. }
  rewrite /abs_carry in Hc.
  exact: abs_chain_joint_exact add_step add_bit QFalse false
    add_step_realize Hinit_only carry_seq
    testbit_carry_seq_0 testbit_carry_seq_succ
    testbit_carry_seq_low_invariant a1 a2 i b1 b2 c Hb1 Hb2 Hc.
Qed.

(** Exactness of [result_bit]: at every bit, the per-bit abstract sum
    captures exactly the set of values of [testbit (p+q) i] as
    [(p, q)] ranges over [γ a1 × γ a2]. *)
(** ** Generic exactness of [chain_result_bit].

    Given the Z-level bit identity and chain recurrence, the per-bit
    abstract result is exactly the set of concrete testbits of [op p q]
    for [(p, q)] in the product γ-set. *)
Lemma chain_result_bit_exact
  (step : bit_step) (f : bit_step_concrete)
  (init : quadrivalent) (init_b : bool)
  (Hstep  : step_sound step f)
  (Hreal  : step_realize step f)
  (Hinit_mem : init_b ∈ γ[qv_abs] init)
  (Hinit_only : forall c, c ∈ γ[qv_abs] init -> c = init_b)
  (op chain   : Z -> Z -> Z)
  (Hbit : forall p q i,
      testbit (op p q) i =
        xorb (xorb (testbit p i) (testbit q i)) (testbit (chain p q) i))
  (Hchain0    : forall p q, testbit (chain p q) 0 = init_b)
  (Hchainrec  : forall p q j,
      testbit (chain p q) (S j) =
        f (testbit p j) (testbit q j) (testbit (chain p q) j))
  (Hchainlow  : forall p q p' q' i,
      (forall j, (j < i)%nat -> testbit p j = testbit p' j) ->
      (forall j, (j < i)%nat -> testbit q j = testbit q' j) ->
      testbit (chain p q) i = testbit (chain p' q') i)
  (a1 a2 : nb_must0_must1) (i : nat) :
  ExactlyRepresents (A := qv_abs)
    (chain_result_bit step init (`a1) (`a2) i)
    (collecting_forward (fun v => testbit v i)
       (collecting_binary_forward op (γ[kb_abs] (`a1)) (γ[kb_abs] (`a2)))).
Proof.
  rewrite /ExactlyRepresents. to_set. split.
  - move=> b Hb. unfold_set.
    move: Hb. rewrite /chain_result_bit => Hb.
    have [Hf _] := abs_xorb_exact
      (abs_xorb (kb_testbit (`a1) i) (kb_testbit (`a2) i))
      (abs_chain step init (`a1) (`a2) i).
    have := Hf b Hb. unfold_set => [[xx [c [Hxx [Hc Heq]]]]]. subst b.
    have [Hf' _] := abs_xorb_exact (kb_testbit (`a1) i) (kb_testbit (`a2) i).
    have := Hf' xx Hxx. unfold_set => [[b1 [b2 [Hb1 [Hb2 Heq']]]]]. subst xx.
    have [p [q [Hp [Hq [Hpi [Hqi Hci]]]]]] :=
      abs_chain_joint_exact step f init init_b Hreal Hinit_only
        chain Hchain0 Hchainrec Hchainlow a1 a2 i b1 b2 c Hb1 Hb2 Hc.
    exists (op p q). split.
    + by exists p, q.
    + by rewrite Hbit Hpi Hqi Hci.
  - move=> b. unfold_set => [[v [[p [q [Hp [Hq Hsum]]]] Hv]]]. subst.
    exact: chain_result_bit_sound step f init init_b Hstep Hinit_mem
      op chain Hbit Hchain0 Hchainrec (`a1) (`a2) p q Hp Hq i.
Qed.

(** Paper: Lemma 4 (Capture uncertainty) at the result-bit level. *)
Lemma result_bit_exact (a1 a2 : nb_must0_must1) i :
  ExactlyRepresents (A := qv_abs)
    (result_bit (`a1) (`a2) i)
    (collecting_forward (fun v => testbit v i)
       (collecting_binary_forward Z.add (γ[kb_abs] (`a1)) (γ[kb_abs] (`a2)))).
Proof.
  have Hinit_mem : false ∈ γ[qv_abs] QFalse by unfold_set.
  have Hinit_only : forall c', c' ∈ γ[qv_abs] QFalse -> c' = false.
  { move=> c'. unfold_set. }
  exact: chain_result_bit_exact add_step add_bit QFalse false
    add_step_sound add_step_realize Hinit_mem Hinit_only
    Z.add carry_seq
    testbit_add_xor_carry testbit_carry_seq_0 testbit_carry_seq_succ
    testbit_carry_seq_low_invariant a1 a2 i.
Qed.

(** ** Equivalence of closed-form [kb_add] and recursive [result_bit]
       (Vishwanathan Lemma 5).

    The closed-form algorithm matches the per-bit recursive abstraction.
    The key Z-level identity is that [must0_1 + must0_2 = sv + sm], from
    which a carry-bit XOR invariant follows; this lets us eliminate the
    internal carry chains of [kb_add] from the bit-level expression. *)

(** [must0 kb = must1 kb + unknown_bits kb] for non-bottom [kb] (the two
    have disjoint bit patterns and union back to [must0]). *)
Lemma kb_must0_decomp (kb : must0_must1) :
  kb_non_bottom kb -> must0 kb = (must1 kb + unknown_bits kb)%Z.
Proof.
  move=> Hnb.
  have Hland : Z.land (must1 kb) (unknown_bits kb) = 0%Z.
  { apply Z_testbit_ext => i.
    rewrite testbit_land /unknown_bits testbit_lxor testbit_0.
    move: (Hnb i). rewrite /kb_testbit.
    by case_kb_testbit kb i. }
  have := Z.add_lor_land (must1 kb) (unknown_bits kb).
  rewrite Hland Z.add_0_r => Hsum. rewrite -Hsum.
  apply Z_testbit_ext => i.
  rewrite testbit_lor /unknown_bits testbit_lxor.
  move: (Hnb i). rewrite /kb_testbit.
  by case_kb_testbit kb i.
Qed.

(** Sigma decomposition: [sv + sm = must0 kb1 + must0 kb2].
    Paper: the σ identity behind Lemma 5 — [Σ = sv + sm] coincides
    with the value-mask sum at the [must0] endpoint of γ. *)
Lemma kb_add_sigma_eq (kb1 kb2 : must0_must1) :
  kb_non_bottom kb1 -> kb_non_bottom kb2 ->
  (must1 kb1 + must1 kb2 + (unknown_bits kb1 + unknown_bits kb2))%Z
  = (must0 kb1 + must0 kb2)%Z.
Proof.
  move=> Hnb1 Hnb2.
  rewrite (kb_must0_decomp kb1 Hnb1) (kb_must0_decomp kb2 Hnb2). lia.
Qed.

(** Carry-XOR invariant. The two ways of writing the sum [sigma]
    (as [sv + sm] or as [must0 kb1 + must0 kb2]) yield the same bit
    at every position, which after the full-adder identity collapses
    to a XOR relation among the four carry chains.
    Paper: Lemma 5 (Equivalence of mask expressions) — shows
    [(sv ⊕ Σ) | P.m | Q.m  =  (sv_c ⊕ Σ_c) | P.m | Q.m]. The XOR
    identity below is its bit-level core. *)
Lemma kb_add_carry_xor_invariant (kb1 kb2 : must0_must1) (i : nat) :
  kb_non_bottom kb1 -> kb_non_bottom kb2 ->
  xorb (testbit (carry_seq (unknown_bits kb1) (unknown_bits kb2)) i)
       (testbit (carry_seq (must1 kb1 + must1 kb2)
                           (unknown_bits kb1 + unknown_bits kb2)) i)
  = xorb (testbit (carry_seq (must0 kb1) (must0 kb2)) i)
         (testbit (carry_seq (must1 kb1) (must1 kb2)) i).
Proof.
  move=> Hnb1 Hnb2.
  set sv := (must1 kb1 + must1 kb2)%Z.
  set sm := (unknown_bits kb1 + unknown_bits kb2)%Z.
  have Hsig : (sv + sm)%Z = (must0 kb1 + must0 kb2)%Z by exact: kb_add_sigma_eq.
  have Hsv := testbit_add_xor_carry (must1 kb1) (must1 kb2) i.
  have Hsm := testbit_add_xor_carry (unknown_bits kb1) (unknown_bits kb2) i.
  have Hsig_sv_sm := testbit_add_xor_carry sv sm i.
  have Hsig_m0 := testbit_add_xor_carry (must0 kb1) (must0 kb2) i.
  have Hu1 : testbit (unknown_bits kb1) i =
             xorb (testbit (must0 kb1) i) (testbit (must1 kb1) i)
    by rewrite /unknown_bits testbit_lxor.
  have Hu2 : testbit (unknown_bits kb2) i =
             xorb (testbit (must0 kb2) i) (testbit (must1 kb2) i)
    by rewrite /unknown_bits testbit_lxor.
  have Heq : testbit (sv + sm) i = testbit (must0 kb1 + must0 kb2) i
    by rewrite Hsig.
  move: Heq. rewrite Hsig_sv_sm Hsig_m0 Hsv Hsm Hu1 Hu2.
  by case_kb2_testbit kb1 kb2 i;
     case_testbits i (carry_seq (must0 kb1) (must0 kb2))
                     (carry_seq (must1 kb1) (must1 kb2))
                     (carry_seq (unknown_bits kb1) (unknown_bits kb2))
                     (carry_seq sv sm).
Qed.

(** Closed-form [kb_add] matches per-bit [result_bit].
    Paper: Lemma 5 (closed form ↔ per-bit equivalence) — bit [i] of the
    σ-decomposed result equals the abstract per-bit computation. *)
Lemma kb_testbit_kb_add (kb1 kb2 : must0_must1) (i : nat) :
  kb_non_bottom kb1 -> kb_non_bottom kb2 ->
  kb_testbit (kb_add kb1 kb2) i = result_bit kb1 kb2 i.
Proof.
  move=> Hnb1 Hnb2.
  have Hinv := kb_add_carry_xor_invariant kb1 kb2 i Hnb1 Hnb2.
  rewrite /result_bit /chain_result_bit /abs_carry /=.
  have := kb_testbit_kb_carry kb1 kb2 i Hnb1 Hnb2.
  rewrite /abs_carry => <-.
  rewrite /kb_testbit /kb_add /kb_carry /=.
  set m0_1 := testbit (must0 kb1) i.
  set m1_1 := testbit (must1 kb1) i.
  set m0_2 := testbit (must0 kb2) i.
  set m1_2 := testbit (must1 kb2) i.
  set k0 := testbit (carry_seq (must0 kb1) (must0 kb2)) i.
  set k1 := testbit (carry_seq (must1 kb1) (must1 kb2)) i.
  set alpha := testbit (carry_seq (unknown_bits kb1) (unknown_bits kb2)) i.
  set beta := testbit (carry_seq (must1 kb1 + must1 kb2)
                                 (unknown_bits kb1 + unknown_bits kb2)) i.
  have Hu1 : testbit (unknown_bits kb1) i = xorb m0_1 m1_1
    by rewrite /unknown_bits testbit_lxor.
  have Hu2 : testbit (unknown_bits kb2) i = xorb m0_2 m1_2
    by rewrite /unknown_bits testbit_lxor.
  rewrite -/m0_1 -/m1_1 -/m0_2 -/m1_2 -/k0 -/k1.
  repeat ((rewrite !testbit_lor) ||
          (rewrite !testbit_land) ||
          (rewrite !testbit_lnot) ||
          (rewrite !testbit_lxor)).
  rewrite !testbit_add_xor_carry !Hu1 !Hu2.
  rewrite /m0_1 /m1_1 /m0_2 /m1_2 /k0 /k1 /alpha /beta in Hinv |- *.
  have HNB1 := non_bottom_no_bad_pair kb1 i Hnb1.
  have HNB2 := non_bottom_no_bad_pair kb2 i Hnb2.
  have Hnb_kc : kb_non_bottom (kb_carry kb1 kb2)
    := NonEmpty.nonempty_lift_binary_sound kb_ad kb_non_bottom
         kb_non_bottom_non_empty kb_carry carry_seq
         (Hsound := kb_carry_sound) kb1 kb2 Hnb1 Hnb2.
  have HNBc := non_bottom_no_bad_pair (kb_carry kb1 kb2) i Hnb_kc.
  apply /qv_eqbP.
  move: HNB1 HNB2 HNBc Hinv.
  case_kb2_testbit kb1 kb2 i;
  case_testbits i (carry_seq (must0 kb1) (must0 kb2))
                  (carry_seq (must1 kb1) (must1 kb2))
                  (carry_seq (unknown_bits kb1) (unknown_bits kb2))
                  (carry_seq (must1 kb1 + must1 kb2)
                             (unknown_bits kb1 + unknown_bits kb2)) => //=;
  try discriminate; try tauto; reflexivity.
Qed.

(** Both [kb_add] and [kb_sub] return a tnum in the standard σ-decomposed
    form [{ must1 := rv := σ & ¬η ; must0 := rv | η }]. In this shape the
    "must0 covers must1" property is automatic: any bit set in [must1] is
    set in [must0]. *)
Lemma kb_std_form_non_bottom (sigma eta : Z) :
  kb_non_bottom
    {| must1 := Z.land sigma (Z.lnot eta);
       must0 := Z.lor (Z.land sigma (Z.lnot eta)) eta |}.
Proof.
  move=> i. rewrite /kb_non_bottom /kb_testbit /=.
  rewrite testbit_lor.
  by case: (testbit (Z.land sigma (Z.lnot eta)) i);
     case: (testbit eta i).
Qed.

(** [kb_add] is always non-bottom: it has the standard σ-decomposed shape. *)
Lemma kb_add_non_bottom (kb1 kb2 : must0_must1) : kb_non_bottom (kb_add kb1 kb2).
Proof. exact: kb_std_form_non_bottom. Qed.

(** [kb_add] is the best abstraction of [Z.add] on non-bottom known bits. *)
Lemma kb_add_best (a1 a2 : nb_must0_must1) :
  BestAbstraction (A := kb_ad)
    (kb_add (`a1) (`a2))
    (collecting_binary_forward Z.add (γ[kb_abs] (`a1)) (γ[kb_abs] (`a2))).
Proof.
  apply: is_alpha_is_best_abstraction.
  have Hnb1 := proj2_sig a1. have Hnb2 := proj2_sig a2.
  have Hnb_add := kb_add_non_bottom (`a1) (`a2).
  apply (kb_is_alpha_of_perbit (exist _ (kb_add (`a1) (`a2)) Hnb_add)).
  move=> i.
  rewrite kb_testbit_kb_add //.
  exact: result_bit_exact.
Qed.

(** Promote an [IsAlpha] proven only on non-bottom inputs to the
    full [binary_overapproximation] over all inputs: bottom inputs
    have empty γ, so any concrete output trivially comes from a
    non-bottom pair, where the [IsAlpha] hypothesis applies. *)
Lemma kb_sound_of_is_alpha
  (kbop : must0_must1 -> must0_must1 -> must0_must1)
  (zop  : Z -> Z -> Z)
  (Halpha : forall a2 a1 : nb_must0_must1,
     IsAlpha (A := kb_ad)
       (kbop (`a2) (`a1))
       (collecting_binary_forward zop (γ[kb_abs] (`a2)) (γ[kb_abs] (`a1)))) :
  binary_overapproximation kb_ad kb_ad kb_ad kbop (collecting_binary_forward zop).
Proof.
  move=> kb2 kb1. rewrite /Overapproximates /= => v Hv. unfold_set in Hv.
  destruct Hv as [p [q [Hp [Hq Hop]]]]. subst.
  have Hnb1 : kb_non_bottom kb1 by apply kb_non_bottom_non_empty; exists q.
  have Hnb2 : kb_non_bottom kb2 by apply kb_non_bottom_non_empty; exists p.
  have /is_alpha_overapproximates Hover :=
    Halpha (exist _ kb2 Hnb2) (exist _ kb1 Hnb1).
  apply Hover. unfold_set. by exists p, q.
Qed.

(** Soundness of [kb_add] over [Z.add] for all inputs (including bottom). *)
Lemma kb_add_sound :
  binary_overapproximation kb_ad kb_ad kb_ad kb_add
    (collecting_binary_forward Z.add).
Proof.
  apply: kb_sound_of_is_alpha => a2 a1.
  apply: best_abstraction_is_is_alpha. exact: kb_add_best.
Qed.

(** *** Non-bottom lift *)
Definition nb_kb_add : nb_must0_must1 -> nb_must0_must1 -> nb_must0_must1 :=
  NonEmpty.nonempty_lift_total_binary kb_ad kb_non_bottom
    kb_non_bottom_non_empty kb_add Z.add (Hsound:=kb_add_sound).

(** Gamma of non-bottom lift equals raw kb gamma. *)
Lemma gamma_nbkb_add a2 Hnb2 a1 Hnb1 v :
  v ∈ γ[nbkb] (nb_kb_add (exist _ a2 Hnb2) (exist _ a1 Hnb1)) <->
  v ∈ γ[kb_abs] (kb_add a2 a1).
Proof. done. Qed.

(** *** Z-level abstract borrow [kb_borrow]

    The concrete borrow sequence of [p - q] has bit [i] holding the borrow
    into bit [i]: [borrow_seq p q = Z.lxor (Z.lxor (p - q) p) q].
    We abstract it by a [must0_must1] whose [must1] is the
    borrow-of-[v1 - v2] (minimum borrows) and whose [must0] is the
    borrow-of-(must0 kb1 - must0 kb2). *)

Definition kb_borrow (kb1 kb2 : must0_must1) : must0_must1 :=
  {| must1 := borrow_seq (must0 kb1) (must1 kb2);
     must0 := borrow_seq (must1 kb1) (must0 kb2) |}.

(** Per-bit equivalence between the Z-level [kb_borrow] and the recursive
    [abs_borrow]. *)
Lemma kb_testbit_kb_borrow (kb1 kb2 : must0_must1) (i : nat) :
  kb_non_bottom kb1 -> kb_non_bottom kb2 ->
  kb_testbit (kb_borrow kb1 kb2) i = abs_borrow kb1 kb2 i.
Proof.
  move=> HNB1 HNB2.
  rewrite /abs_borrow.
  elim: i => [|i IH].
  - rewrite /kb_testbit /kb_borrow /must0 /must1.
    by rewrite !testbit_borrow_seq_0.
  - rewrite /kb_testbit /kb_borrow /=.
    rewrite !testbit_borrow_seq_succ.
    rewrite -IH.
    apply /qv_eqbP.
    move: (HNB1 i) (HNB2 i). rewrite /kb_testbit.
    have [p Hp] := proj1 (kb_non_bottom_non_empty kb1) HNB1.
    have [q Hq] := proj1 (kb_non_bottom_non_empty kb2) HNB2.
    have [b [Hb0 [Hbrec _]]] := concrete_borrow_seq p q.
    have Hinit : false ∈ γ[qv_abs] QFalse by unfold_set.
    have BNB : abs_chain sub_step QFalse kb1 kb2 i <> QBottom
      := in_gamma_not_bottom _ _ (abs_chain_sound sub_step sub_bit QFalse false
          sub_step_sound Hinit kb1 kb2 p q Hp Hq b Hb0 Hbrec i).
    move: BNB. rewrite -IH /kb_testbit /kb_borrow /=.
    case_kb2_testbit kb1 kb2 i;
    case_testbits i (borrow_seq (must1 kb1) (must0 kb2))
                    (borrow_seq (must0 kb1) (must1 kb2)) => //=;
    try discriminate; try tauto; reflexivity.
Qed.

(** [kb_borrow] is a sound binary overapproximation of [borrow_seq]. *)
Lemma kb_borrow_sound :
  binary_overapproximation kb_ad kb_ad kb_ad kb_borrow
    (collecting_binary_forward borrow_seq).
Proof.
  move=> kb2 kb1 v Hv. unfold_set in Hv.
  destruct Hv as [p [q [Hp [Hq Hv]]]]. subst.
  have Hnb2 : kb_non_bottom kb2 by apply kb_non_bottom_non_empty; exists p.
  have Hnb1 : kb_non_bottom kb1 by apply kb_non_bottom_non_empty; exists q.
  unfold_set => i. rewrite kb_testbit_kb_borrow //.
  exact: (abs_chain_sound sub_step sub_bit QFalse false sub_step_sound
           (ltac:(unfold_set) : false ∈ γ[qv_abs] QFalse)
           kb2 kb1 p q Hp Hq (borrow_seq p q)
           (testbit_borrow_seq_0 p q) (testbit_borrow_seq_succ p q) i).
Qed.

(** *** Closed-form [kb_sub] — Vishwanathan et al., §III-B sketch.

    The closed form follows the same σ-decomposition pattern as [kb_add]:
    [dv = must1 kb1 - must0 kb2] (minimum of γ subtraction),
    [dm = unknown_bits kb1 + unknown_bits kb2] (unknown-bit contributions),
    [σ = dv + dm], then [χ = σ ⊕ dv], [η = χ | m1 | m2], and the
    result [must1 = dv & ~η], [must0 = rv | η].

    The paper's [tnum_sub] is in the extended technical report; the
    body here matches the same σ/χ/η template as [tnum_add] (Listing 1)
    with [sv] replaced by [dv] (min of γ subtraction). *)

Definition kb_sub (kb1 kb2 : must0_must1) : must0_must1 :=
  let v1    := must1 kb1 in let m1 := unknown_bits kb1 in
  let v2    := must1 kb2 in let m2 := unknown_bits kb2 in
  let dv    := (v1 - must0 kb2)%Z in
  let dm    := (m1 + m2)%Z in
  let sigma := (dv + dm)%Z in
  let chi   := Z.lxor sigma dv in
  let eta   := Z.lor chi (Z.lor m1 m2) in
  let rv    := Z.land dv (Z.lnot eta) in
  {| must1 := rv;
     must0 := Z.lor rv eta |}.

(** Sigma decomposition for subtraction:
    [dv + dm = must0 kb1 - must1 kb2].
    Paper: σ identity behind the sub-version of Lemma 5 — [Σ = dv + dm]
    coincides with the [must0 − must1] endpoint pairing. *)
Lemma kb_sub_sigma_eq (kb1 kb2 : must0_must1) :
  kb_non_bottom kb1 -> kb_non_bottom kb2 ->
  (must1 kb1 - must0 kb2 + (unknown_bits kb1 + unknown_bits kb2))%Z
  = (must0 kb1 - must1 kb2)%Z.
Proof.
  move=> Hnb1 Hnb2.
  rewrite (kb_must0_decomp kb2 Hnb2) (kb_must0_decomp kb1 Hnb1). lia.
Qed.

(** Borrow-XOR invariant. The two ways of writing the sigma value
    (as [dv + dm] or as [must0 kb1 - must1 kb2]) yield the same bit,
    which after the full-adder/full-subtractor identities yields a
    relation among the four chain sequences (two carry, two borrow).
    Paper: sub-side analog of Lemma 5 (Equivalence of mask expressions). *)
Lemma kb_sub_borrow_xor_invariant (kb1 kb2 : must0_must1) (i : nat) :
  kb_non_bottom kb1 -> kb_non_bottom kb2 ->
  xorb (testbit (carry_seq (unknown_bits kb1) (unknown_bits kb2)) i)
       (testbit (carry_seq (must1 kb1 - must0 kb2)
                           (unknown_bits kb1 + unknown_bits kb2)) i)
  = xorb (testbit (borrow_seq (must0 kb1) (must1 kb2)) i)
         (testbit (borrow_seq (must1 kb1) (must0 kb2)) i).
Proof.
  move=> Hnb1 Hnb2.
  set dv := (must1 kb1 - must0 kb2)%Z.
  set dm := (unknown_bits kb1 + unknown_bits kb2)%Z.
  have Hsig : (dv + dm)%Z = (must0 kb1 - must1 kb2)%Z by exact: kb_sub_sigma_eq.
  have Hsig_dv_dm := testbit_add_xor_carry dv dm i.
  have Hsig_m0 := testbit_sub_xor_borrow (must0 kb1) (must1 kb2) i.
  have Hdv := testbit_sub_xor_borrow (must1 kb1) (must0 kb2) i.
  have Hdm := testbit_add_xor_carry (unknown_bits kb1) (unknown_bits kb2) i.
  have Hu1 : testbit (unknown_bits kb1) i =
             xorb (testbit (must0 kb1) i) (testbit (must1 kb1) i)
    by rewrite /unknown_bits testbit_lxor.
  have Hu2 : testbit (unknown_bits kb2) i =
             xorb (testbit (must0 kb2) i) (testbit (must1 kb2) i)
    by rewrite /unknown_bits testbit_lxor.
  have Heq : testbit (dv + dm) i = testbit (must0 kb1 - must1 kb2) i
    by rewrite Hsig.
  move: Heq. rewrite Hsig_dv_dm Hsig_m0 Hdv Hdm Hu1 Hu2.
  by case_kb2_testbit kb1 kb2 i;
     case_testbits i (carry_seq (unknown_bits kb1) (unknown_bits kb2))
                     (carry_seq dv dm)
                     (borrow_seq (must0 kb1) (must1 kb2))
                     (borrow_seq (must1 kb1) (must0 kb2)).
Qed.

(** Closed-form [kb_sub] matches per-bit [result_bit_sub].
    Paper: sub-side analog of Lemma 5 (closed form ↔ per-bit). *)
Lemma kb_testbit_kb_sub (kb1 kb2 : must0_must1) (i : nat) :
  kb_non_bottom kb1 -> kb_non_bottom kb2 ->
  kb_testbit (kb_sub kb1 kb2) i = result_bit_sub kb1 kb2 i.
Proof.
  move=> Hnb1 Hnb2.
  have Hinv := kb_sub_borrow_xor_invariant kb1 kb2 i Hnb1 Hnb2.
  rewrite /result_bit_sub /chain_result_bit /abs_borrow /=.
  have := kb_testbit_kb_borrow kb1 kb2 i Hnb1 Hnb2.
  rewrite /abs_borrow => <-.
  rewrite /kb_testbit /kb_sub /kb_borrow.
  cbn -[Z.sub].
  set m0_1 := testbit (must0 kb1) i.
  set m1_1 := testbit (must1 kb1) i.
  set m0_2 := testbit (must0 kb2) i.
  set m1_2 := testbit (must1 kb2) i.
  set b0 := testbit (borrow_seq (must0 kb1) (must1 kb2)) i.
  set b1 := testbit (borrow_seq (must1 kb1) (must0 kb2)) i.
  set alpha := testbit (carry_seq (unknown_bits kb1) (unknown_bits kb2)) i.
  set beta := testbit (carry_seq (must1 kb1 - must0 kb2)
                                 (unknown_bits kb1 + unknown_bits kb2)) i.
  have Hu1 : testbit (unknown_bits kb1) i = xorb m0_1 m1_1
    by rewrite /unknown_bits testbit_lxor.
  have Hu2 : testbit (unknown_bits kb2) i = xorb m0_2 m1_2
    by rewrite /unknown_bits testbit_lxor.
  rewrite -/m0_1 -/m1_1 -/m0_2 -/m1_2 -/b0 -/b1.
  repeat ((rewrite !testbit_lor) ||
          (rewrite !testbit_land) ||
          (rewrite !testbit_lnot) ||
          (rewrite !testbit_lxor)).
  rewrite (testbit_add_xor_carry (must1 kb1 - must0 kb2)%Z
             (unknown_bits kb1 + unknown_bits kb2)%Z i).
  rewrite (testbit_add_xor_carry (unknown_bits kb1) (unknown_bits kb2) i).
  rewrite !testbit_sub_xor_borrow.
  rewrite !Hu1 !Hu2.
  rewrite /m0_1 /m1_1 /m0_2 /m1_2 /b0 /b1 /alpha /beta in Hinv |- *.
  have HNB1 := non_bottom_no_bad_pair kb1 i Hnb1.
  have HNB2 := non_bottom_no_bad_pair kb2 i Hnb2.
  have Hnb_kb : kb_non_bottom (kb_borrow kb1 kb2)
    := NonEmpty.nonempty_lift_binary_sound kb_ad kb_non_bottom
         kb_non_bottom_non_empty kb_borrow borrow_seq
         (Hsound := kb_borrow_sound) kb1 kb2 Hnb1 Hnb2.
  have HNBb := non_bottom_no_bad_pair (kb_borrow kb1 kb2) i Hnb_kb.
  apply /qv_eqbP.
  move: HNB1 HNB2 HNBb Hinv.
  case_kb2_testbit kb1 kb2 i;
  case_testbits i (borrow_seq (must0 kb1) (must1 kb2))
                  (borrow_seq (must1 kb1) (must0 kb2))
                  (carry_seq (unknown_bits kb1) (unknown_bits kb2))
                  (carry_seq (must1 kb1 - must0 kb2)
                             (unknown_bits kb1 + unknown_bits kb2)) => //=;
  try discriminate; try tauto; reflexivity.
Qed.

(** [kb_sub] is always non-bottom: same standard σ-decomposed shape. *)
Lemma kb_sub_non_bottom (kb1 kb2 : must0_must1) : kb_non_bottom (kb_sub kb1 kb2).
Proof. exact: kb_std_form_non_bottom. Qed.

(** [kb_sub] is the best abstraction of [Z.sub] on non-bottom known bits.  *)
Lemma kb_sub_best (a1 a2 : nb_must0_must1) :
  BestAbstraction (A := kb_ad)
    (kb_sub (`a1) (`a2))
    (collecting_binary_forward Z.sub (γ[kb_abs] (`a1)) (γ[kb_abs] (`a2))).
Proof.
  apply: is_alpha_is_best_abstraction.
  have Hnb1 := proj2_sig a1. have Hnb2 := proj2_sig a2.
  have Hnb_sub := kb_sub_non_bottom (`a1) (`a2).
  apply (kb_is_alpha_of_perbit (exist _ (kb_sub (`a1) (`a2)) Hnb_sub)).
  move=> i.
  rewrite kb_testbit_kb_sub //.
  have Hinit_mem : false ∈ γ[qv_abs] QFalse by unfold_set.
  have Hinit_only : forall c', c' ∈ γ[qv_abs] QFalse -> c' = false.
  { move=> c'. unfold_set. }
  exact: chain_result_bit_exact sub_step sub_bit QFalse false
    sub_step_sound sub_step_realize Hinit_mem Hinit_only
    Z.sub borrow_seq testbit_sub_xor_borrow
    testbit_borrow_seq_0 testbit_borrow_seq_succ
    testbit_borrow_seq_low_invariant a1 a2 i.
Qed.

(** Soundness of [kb_sub] over [Z.sub] for all inputs (including bottom). *)
Lemma kb_sub_sound :
  binary_overapproximation kb_ad kb_ad kb_ad kb_sub
    (collecting_binary_forward Z.sub).
Proof.
  apply: kb_sound_of_is_alpha => a2 a1.
  apply: best_abstraction_is_is_alpha. exact: kb_sub_best.
Qed.

(** *** Non-bottom lift *)
Definition nb_kb_sub : nb_must0_must1 -> nb_must0_must1 -> nb_must0_must1 :=
  NonEmpty.nonempty_lift_total_binary kb_ad kb_non_bottom
    kb_non_bottom_non_empty kb_sub Z.sub (Hsound:=kb_sub_sound).

(** Gamma of non-bottom lift equals raw kb gamma. *)
Lemma gamma_nbkb_sub a2 Hnb2 a1 Hnb1 v :
  v ∈ γ[nbkb] (nb_kb_sub (exist _ a2 Hnb2) (exist _ a1 Hnb1)) <->
  v ∈ γ[kb_abs] (kb_sub a2 a1).
Proof. done. Qed.

(** * Negative precision results for [kb_add].

    [kb_add] is the best transfer function ([kb_add_best] above); what
    follows delimits how far that goes: it is neither γ-exact nor
    α-complete. *)

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
