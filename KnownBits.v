(* KnownBits.v - Known-bits abstraction for Z using must0_must1 representation *)

(* STATUS: the known-bits domain (must0, must1).
   order : pointwise quadrivalent, exact   lattice : pointwise join/meet
   γ-injective on non-bottom elements, with the sufficient direction of the
   α-characterization.

   All transfer functions now live in Transfer_function/KnownBits/; what is
   left here is the abstraction itself plus the [testbit] / [setbit] toolkit
   and the [bitwise_to_boolean] hint database they share.
   lor, land, lxor : sound + exact       BitwiseTheory.v
   add, sub        : sound + best        AddSubTheory.v
     (add is NOT γ-exact and NOT α-complete; same file) *)

Require Import Abstraction.
Require Import autoreflect.
Require Import Quadrivalent.
Require Import SvaQuadrivalent.
From Stdlib Require Import ssreflect ssrbool.
Require Import Stdlib.ZArith.ZArith.
From Stdlib Require Import Lia. (* lia/nia; avoid Psatz which loads Reals axioms *)
Open Scope Z_scope.

(** * Known-bits abstraction

    A known-bits abstract value tracks, for each bit position of an
    unbounded integer, whether the bit is known to be 0, known to be 1,
    or unknown. The representation is a pair (must0, must1) of Z integers:

    - must0 bit i = 0  =>  concrete bit i must be 0
    - must1 bit i = 1  =>  concrete bit i must be 1

    Per-bit mapping to quadrivalent:
    - (0,0) = known 0  (QFalse)
    - (1,1) = known 1  (QTrue)
    - (0,1) = bottom   (QBottom, contradictory)
    - (1,0) = top       (QTop, unknown)

    ** Relation to Vishwanathan et al. 2022

    The arithmetic operations [kb_add] / [kb_sub] and their soundness +
    optimality proofs follow:

      Vishwanathan, Shachnai, Narayana, Nagarakatte, "Sound, Precise,
      and Fast Abstract Interpretation with Tristate Numbers", CGO 2022.
      (PDF in this repository:
      [vishwanathan_et_al2022sound_precise_fast_abstract_interpretation_tristate_numbers.pdf])

    The paper uses the [(value, mask)] representation [(P.v, P.m)] where
    [P.v] holds the known bits and [P.m] marks the unknown bits. We use
    [(must0, must1)] instead, where [must0]/[must1] mark which bits are
    forced to 0/1; the masks coincide via
    [unknown_bits kb = Z.lxor (must0 kb) (must1 kb)]. The σ-decomposition
    variables (sv, sm, Σ, χ, η, R.v, R.m) used by the kernel's
    [tnum_add] / [tnum_sub] map onto our local [let]-bindings in
    [kb_add] / [kb_sub]:

      Paper             Code  (in [kb_add] / [kb_sub])
      ---------------   ------------------------------------
      P.v   = v1         must1 kb1
      P.m   = m1         unknown_bits kb1
      sv    = P.v + Q.v  sv     (kb_add)
      sv    = P.v - Q.m  dv     (kb_sub, "minimum subtraction")
      sm    = P.m + Q.m  sm / dm
      Σ     = sv + sm    sigma
      χ     = Σ ⊕ sv     chi
      η     = χ | P.m | Q.m   eta
      R.v   = sv & ~η    must1 of the result
      R.m   = η          must0 ≡ rv | η   (we store must0, not the mask)

    Per-lemma cross-references to paper results appear as
    "Paper: …" markers on the relevant lemmas below
    (Definition 1: full adder; Lemma 2: minimum carries; Lemma 4:
    capture uncertainty; Lemma 5: equivalence of mask expressions;
    Theorem 6: soundness + optimality of tnum_add). The paper notes
    (§III-B) that the proof for subtraction is "very similar in
    structure"; we make that similarity literal via a shared per-bit
    chain framework ([Section BitChain] below). *)

Record must0_must1 := {
  must0 : Z;
  must1 : Z
}.

(** ** Per-bit quadrivalent extraction *)

(** Usual testbit is defined on Z, which requires carrying the side
condition that the index is positive. We don't need that if the index
is a nat. We port all useful lemmas about testbit here. *)
Section Testbit.
  Definition testbit v (i : nat) : bool := Z.testbit v (Z.of_nat i).

  Lemma testbit_0 (i:nat): testbit 0 i = false.
  Proof. apply Z.bits_0. Qed.
  
  Lemma testbit_m1 (i:nat): testbit (-1) i = true.
  Proof. apply Z.bits_m1. lia. Qed.

  (** Bitvector extensionality. *)
  Lemma testbit_ext (a b : Z) :
    (forall i : nat, testbit a i = testbit b i) <-> a = b.
  Proof.
    split.
    - move=> H. apply Z.bits_inj' => n Hn.
      have := H (Z.to_nat n). rewrite /testbit Z2Nat.id //.
    - by move=> ->.
  Qed.

  Lemma Z_testbit_ext (a b : Z) :
    (forall i : nat, testbit a i = testbit b i) -> a = b.
  Proof. by move/testbit_ext. Qed.
End Testbit.


Section Setbit.
  (* Not [Local]: [Transfer_function/KnownBits/AddSubTheory.v] builds its
     bit-realization witnesses with it. *)
  Definition setbit_to (v : Z) (i : nat) (b : bool) : Z :=
    if b then Z.setbit v (Z.of_nat i)
    else Z.clearbit v (Z.of_nat i).

  (* Read over write axioms applied to bitvector. *)
  Lemma testbit_over_setbit_same v i b :
    testbit (setbit_to v i b) i = b.
  Proof.
    rewrite /setbit_to /testbit.
    case: b.
    - apply Z.setbit_eq. lia.
    - apply Z.clearbit_eq. 
  Qed.

  Lemma testbit_over_setbit_different v i j b :
    i <> j -> testbit (setbit_to v i b) j = testbit v j.
  Proof.
    move=> Hne. rewrite /setbit_to /testbit.
    have Hne': Z.of_nat i <> Z.of_nat j by lia.
    case: b.
    - apply Z.setbit_neq; lia.
    - apply Z.clearbit_neq; lia.
  Qed.


  (** Testbit + bitwise operations. *)
  Lemma testbit_lor a b i : testbit (Z.lor a b) i = testbit a i || testbit b i.
  Proof. apply Z.lor_spec. Qed.

  Lemma testbit_land a b i : testbit (Z.land a b) i = testbit a i && testbit b i.
  Proof. apply Z.land_spec. Qed.

  Lemma testbit_lxor a b i : testbit (Z.lxor a b) i = xorb (testbit a i) (testbit b i).
  Proof. apply Z.lxor_spec. Qed.

  Lemma testbit_lnot a i : testbit (Z.lnot a) i = negb (testbit a i).
  Proof. rewrite /testbit. apply Z.lnot_spec. lia. Qed.

End Setbit.

(** Hint database for rewriting [testbit] of Z bitwise/add/carry ops
    into boolean expressions.  Hints are added incrementally as lemmas
    are proved.  Use [autorewrite with bitwise_to_boolean]. *)
Create HintDb bitwise_to_boolean discriminated.
Hint Rewrite @testbit_lor @testbit_land @testbit_lxor @testbit_lnot
  : bitwise_to_boolean.

Definition kb_testbit (kb : must0_must1) (i : nat) : quadrivalent :=
  match testbit (must0 kb) i, testbit (must1 kb) i with
  | false, false => QFalse
  | true,  true  => QTrue
  | false, true  => QBottom
  | true,  false => QTop
  end.

(** [case_testbits i z1 .. zn] case-splits on [testbit] of the given Z
    expressions at position [i].  Supports 1–4 arguments via overloading. *)
Tactic Notation "case_testbits" ident(i) constr(z1) :=
  case: (testbit z1 i).
Tactic Notation "case_testbits" ident(i) constr(z1) constr(z2) :=
  case: (testbit z1 i); case: (testbit z2 i).
Tactic Notation "case_testbits" ident(i) constr(z1) constr(z2) constr(z3) :=
  case: (testbit z1 i); case: (testbit z2 i); case: (testbit z3 i).
Tactic Notation "case_testbits" ident(i) constr(z1) constr(z2) constr(z3) constr(z4) :=
  case: (testbit z1 i); case: (testbit z2 i); case: (testbit z3 i); case: (testbit z4 i).

(** Shorthands for the common case of splitting known-bits projections.
    [case_kb_testbit kb i] gives 4 subgoals (one per quadrivalent value);
    [case_kb2_testbit kb1 kb2 i] gives 16. *)
Ltac case_kb_testbit kb i :=
  case_testbits i (must0 kb) (must1 kb).

Ltac case_kb2_testbit kb1 kb2 i :=
  case_testbits i (must0 kb1) (must1 kb1) (must0 kb2) (must1 kb2).


(** Extensionality: two must0_must1 are equal iff kb_testbit agrees everywhere. *)
Lemma kb_testbit_ext (kb1 kb2 : must0_must1) :
  (forall i : nat, kb_testbit kb1 i = kb_testbit kb2 i) <-> kb1 = kb2.
Proof.
  split.
  - move=> H.
    have Hm0 : must0 kb1 = must0 kb2.
    { apply testbit_ext => i. have := H i. rewrite /kb_testbit.
      by case_kb2_testbit kb1 kb2 i. }
    have Hm1 : must1 kb1 = must1 kb2.
    { apply testbit_ext => i. have := H i. rewrite /kb_testbit.
      by case_kb2_testbit kb1 kb2 i. }
    destruct kb1, kb2. simpl in *. by subst.
  - by move=> ->.
Qed.

(** ** Gamma (concretization) *)

(** Gamma is defined pointwise via the quadrivalent concretization:
    a concrete integer [v] is in [γ kb] iff at every bit position,
    [testbit v i] belongs to [γ(kb_testbit kb i)]. *)
Definition kb_gamma (kb : must0_must1) : ℘ Z :=
  {[ v | forall i : nat, testbit v i ∈ γ[qv_abs] (kb_testbit kb i) ]}.

Definition kb_abs : abstraction Z := BuildAbstraction kb_gamma.


(** kb_testbit is used to define gamma, but is also a sound transfer
function abstracting testbit. *)
Lemma kb_testbit_sound (i : nat) :
  unary_overapproximation kb_abs qv_abs
    (fun kb => kb_testbit kb i)
    (collecting_forward (fun v => testbit v i)).
Proof.
  move=> kb. rewrite /Overapproximates. to_set. unfold_set.
  move=> b [v [Hv Heq]]. subst. exact (Hv i).
Qed.

(** ** Per-bit equivalence with implication form *)

Lemma kb_testbit_gamma_iff (kb : must0_must1) (v : Z) (i : nat) :
  ((testbit (must0 kb) i = false -> testbit v i = false) /\
   (testbit (must1 kb) i = true  -> testbit v i = true))
  <->
  testbit v i ∈ γ[qv_abs] (kb_testbit kb i).
Proof.
  rewrite /kb_testbit.
  case_kb_testbit kb i;
    unfold_set; case: (testbit v i); intuition discriminate.
Qed.

Lemma kb_gamma_impl (kb : must0_must1) (v : Z) :
  v ∈ γ[kb_abs] kb <->
  forall i : nat,
    (testbit (must0 kb) i = false -> testbit v i = false) /\
    (testbit (must1 kb) i = true  -> testbit v i = true).
Proof.
  unfold_set.
  split; move=> H i; move: (H i); by apply kb_testbit_gamma_iff.
Qed.

(** ** Elimination lemmas *)

Lemma kb_gamma_must0 (kb : must0_must1) (v : Z) (i : nat) :
  v ∈ γ[kb_abs] kb ->
  testbit (must0 kb) i = false ->
  testbit v i = false.
Proof.
  rewrite kb_gamma_impl. move=> H Hm0. have [H0 _] := H i. by apply H0.
Qed.

Lemma kb_gamma_must1 (kb : must0_must1) (v : Z) (i : nat) :
  v ∈ γ[kb_abs] kb ->
  testbit (must1 kb) i = true ->
  testbit v i = true.
Proof.
  rewrite kb_gamma_impl. move=> H Hm1. have [_ H1] := H i. by apply H1.
Qed.

(** Absorption: v ∈ γ(kb) implies v AND must0 = v (v is "below" must0). *)
Lemma kb_gamma_land_must0 (kb : must0_must1) (v : Z) :
  v ∈ γ[kb_abs] kb -> Z.land v (must0 kb) = v.
Proof.
  move=> Hv. apply Z_testbit_ext => i. rewrite testbit_land.
  case Hm0: (testbit (must0 kb) i).
  - by rewrite Bool.andb_true_r.
  - rewrite Bool.andb_false_r. symmetry. by apply (kb_gamma_must0 kb v i).
Qed.

(** Absorption: v ∈ γ(kb) implies v OR must1 = v (v is "above" must1). *)
Lemma kb_gamma_lor_must1 (kb : must0_must1) (v : Z) :
  v ∈ γ[kb_abs] kb -> Z.lor v (must1 kb) = v.
Proof.
  move=> Hv. apply Z_testbit_ext => i. rewrite testbit_lor.
  case Hm1: (testbit (must1 kb) i).
  - rewrite Bool.orb_true_r. symmetry. by apply (kb_gamma_must1 kb v i).
  - by rewrite Bool.orb_false_r.
Qed.

(** ** Top and bottom elements *)

Definition kb_top : must0_must1 := {| must0 := -1; must1 := 0 |}.
Definition kb_bottom : must0_must1 := {| must0 := 0; must1 := -1 |}.

Lemma kb_top_full (v : Z) : v ∈ γ[kb_abs] kb_top.
Proof.
  unfold_set. unfold_gamma. move=> i.
  rewrite /kb_top/kb_testbit/must0/must1; simpl.
  rewrite testbit_0. rewrite testbit_m1. done.
Qed.

Lemma kb_bottom_empty (v : Z) : ~ (v ∈ γ[kb_abs] kb_bottom).
Proof.
  unfold_set. unfold_gamma. move /(_ (0%nat)) => H.
  rewrite /kb_bottom/kb_testbit/must0/must1 in H.
  rewrite testbit_0 in H. rewrite testbit_m1 in H. done.
Qed.

(** ** Ordering (pointwise quadrivalent ordering) *)

Definition kb_sqsubseteq (kb1 kb2 : must0_must1) : Prop :=
  forall i : nat, kb_testbit kb1 i ⊑ kb_testbit kb2 i.

Instance kb_sqsubseteq_preorder : PreOrder kb_sqsubseteq.
Proof.
  constructor.
  - move=> x i. reflexivity.
  - move=> x y z Hxy Hyz i. by transitivity (kb_testbit y i).
Qed.

Lemma kb_sqsubseteq_sound (a1 a2 : must0_must1) :
  kb_sqsubseteq a1 a2 -> γ[kb_abs] a1 ⊆ γ[kb_abs] a2.
Proof.
  move=> Hsub c. unfold_set. move=> Hc i.
  move: (Hsub i). rewrite qv_sqsubseteq_exact. unfold_set.
  by apply; apply Hc.
Qed.

Program Instance kb_admixin : abstract_domain_laws (A:=kb_abs) kb_gamma kb_sqsubseteq.
Next Obligation.
  exact kb_sqsubseteq_sound.
Defined.

Definition kb_ad : abstract_domain Z :=
  BuildAbstractDomain kb_gamma kb_sqsubseteq kb_admixin.
Global Hint Unfold kb_ad kb_gamma : unfold_gamma.

(** ** Lattice operations (pointwise quadrivalent) *)

Require Import AbstractLattice.
Require Import QuadrivalentLattice.

Definition kb_join (kb1 kb2 : must0_must1) : must0_must1 :=
  {| must0 := Z.lor (must0 kb1) (must0 kb2);
     must1 := Z.land (must1 kb1) (must1 kb2) |}.

Definition kb_meet (kb1 kb2 : must0_must1) : must0_must1 :=
  {| must0 := Z.land (must0 kb1) (must0 kb2);
     must1 := Z.lor (must1 kb1) (must1 kb2) |}.

Definition kb_equiv (kb1 kb2 : must0_must1) : Prop := kb1 = kb2.

Lemma kb_testbit_join kb1 kb2 i :
  kb_testbit (kb_join kb1 kb2) i =
  QuadrivalentLattice.join (kb_testbit kb1 i) (kb_testbit kb2 i).
Proof.
  rewrite /kb_testbit /kb_join /must0 /must1.
  rewrite testbit_lor testbit_land.
  by case_kb2_testbit kb1 kb2 i.
Qed.

Lemma kb_testbit_meet kb1 kb2 i :
  kb_testbit (kb_meet kb1 kb2) i =
  QuadrivalentLattice.meet (kb_testbit kb1 i) (kb_testbit kb2 i).
Proof.
  rewrite /kb_testbit /kb_meet /must0 /must1.
  rewrite testbit_land testbit_lor.
  by case_kb2_testbit kb1 kb2 i.
Qed.

Instance kb_ajsl_laws : abstract_join_semilattice_laws kb_ad kb_join kb_equiv.
Proof.
  constructor.
  - exact kb_admixin.
  - move=> a1 a2 ->. split; reflexivity.
  - move=> a1 a2 i. rewrite kb_testbit_join.
    destruct (kb_testbit a1 i), (kb_testbit a2 i); done.
  - move=> a1 a2 i. rewrite kb_testbit_join.
    destruct (kb_testbit a1 i), (kb_testbit a2 i); done.
Qed.

Definition kb_al : abstract_lattice Z :=
  BuildAbstractLattice kb_ad kb_join kb_meet kb_equiv kb_ajsl_laws.

Instance kb_join_is_lub : JoinIsLUB kb_al.
Proof.
  move=> a1 a2 c H1 H2 i. rewrite kb_testbit_join.
  have := H1 i. have := H2 i.
  destruct (kb_testbit a1 i), (kb_testbit a2 i), (kb_testbit c i); done.
Qed.

(** ** Non-bottom known-bits *)

Definition kb_non_bottom (kb : must0_must1) : Prop :=
  forall i : nat, kb_testbit kb i <> QBottom.

(** Non-bottom means must1 ⊆_bw must0: if must1 bit is 1, must0 bit is 1. *)
Lemma non_bottom_must1_must0 (kb : must0_must1) (i : nat) :
  kb_non_bottom kb ->
  testbit (must1 kb) i = true -> testbit (must0 kb) i = true.
Proof.
  move=> Hnb Hm1. move: (Hnb i). rewrite /kb_testbit Hm1.
  by case: (testbit (must0 kb) i).
Qed.

(** Contrapositive form of [non_bottom_must1_must0]: a non-bottom kb has
    no bit where [must0 = false ∧ must1 = true]. Used throughout the
    σ-decomposition proofs to eliminate the impossible quadrivalent
    case in [case_kb2_testbit]. *)
Lemma non_bottom_no_bad_pair (kb : must0_must1) (i : nat) :
  kb_non_bottom kb ->
  ~ (testbit (must0 kb) i = false /\ testbit (must1 kb) i = true).
Proof.
  move=> Hnb [H0 H1]. by rewrite (non_bottom_must1_must0 _ _ Hnb H1) in H0.
Qed.

Lemma kb_non_bottom_non_empty (kb : must0_must1) :
  kb_non_bottom kb <-> exists v, v ∈ γ[kb_abs] kb.
Proof.
  split.
  - (** non_bottom -> non_empty: we choose [must1 kb] as witness. *)
    move=> Hnb. exists (must1 kb). rewrite kb_gamma_impl. move=> i. split.
    + (** must0 bit = false -> must1 bit = false *)
      move=> Hm0.
      (** From non_bottom: kb_testbit kb i <> QBottom.
          With must0 bit = false, if must1 bit were true, we'd get QBottom. *)
      move: (Hnb i). rewrite /kb_testbit Hm0.
      by case: (testbit (must1 kb) i).
    + done.
  - (** non_empty -> non_bottom *)
    move=> [v Hv] i Hbot.
    move: Hv. unfold_set. move /(_ i).
    move: Hbot => ->. unfold_set.
Qed.

(** ** Unknown bits. *)

(** When the argument is non-bottom, then we can now the unknown bits
    by a xor of both arguments.  *)
Definition unknown_bits (kb : must0_must1) : Z :=
  Z.lxor (must0 kb) (must1 kb).

Lemma kb_unknown (kb: must0_must1) (i: nat) :
  kb_non_bottom kb ->
  testbit (unknown_bits kb) i = true <-> kb_testbit kb i = QTop.
Proof.
  move/(_ i) => HNB. rewrite /unknown_bits/kb_testbit.
  rewrite /kb_non_bottom/kb_testbit in HNB.
  rewrite testbit_lxor.
  move: HNB.
  case H0: (testbit (must0 kb) i); case H1: (testbit (must1 kb) i) => //=.
Qed.
  

Require Import AbstractionCombination.

Definition nb_must0_must1 : Type := { kb : must0_must1 | kb_non_bottom kb }.
Definition nbkb : abstract_domain Z := NonEmpty.ad kb_ad kb_non_bottom.


(** If bit i is free (QTop) in kb, we can set it to any value
    and stay in gamma. *)
Lemma kb_gamma_set_free_bit kb v i b :
  v ∈ γ[kb_abs] kb ->
  kb_testbit kb i = QTop ->
  setbit_to v i b ∈ γ[kb_abs] kb.
Proof.
  move=> Hv Hfree. unfold_set. move=> j.
  case (Nat.eq_dec i j) => [<- | Hneq].
  - rewrite testbit_over_setbit_same Hfree. unfold_set. done.
  - rewrite testbit_over_setbit_different //. by have := (Hv : v ∈ γ[kb_abs] kb) : _ ; unfold_set.
Qed.

(** [kb_testbit] at position [i] is an exact abstraction of
    [fun v => testbit v i], for non-bottom known-bits. Equivalently:
    [γ[qv_abs](kb_testbit kb i) = { testbit v i | v ∈ γ[kb_abs] kb }]. *)
Lemma kb_testbit_exact (a1 : nb_must0_must1) i :
  ExactlyRepresents (A:=qv_abs) (kb_testbit (`a1) i)
    (collecting_forward (fun v => testbit v i) (γ[kb_abs] (`a1))).
Proof.
  move: a1 => [kb Hnb]. simpl.
  rewrite /ExactlyRepresents. to_set. unfold_set. split.
  - (** Completeness: γ[qv](kb_testbit kb i) ⊆ { testbit v i | v ∈ γ kb } *)
    move=> b Hb.
    (** We start from the inhabited witness w. *)
    have [w Hw] := (proj1 (kb_non_bottom_non_empty kb)) Hnb.
    have Hwi : testbit w i ∈ γ[qv_abs] (kb_testbit kb i) by exact (Hw i).
    case (Bool.bool_dec (testbit w i) b) => [<- | Hneq].
    + by exists w.
    + (** Both b and testbit w i are in γ(kb_testbit kb i),
          so kb_testbit kb i must be QTop. *)
      have Htop: kb_testbit kb i = QTop.
      { have Hnot: testbit w i = ~~b
          by destruct (testbit w i); destruct b; done.
        clear Hneq. rewrite Hnot in Hwi.
        by destruct (kb_testbit kb i); destruct b; unfold_set in *. }
      exists (setbit_to w i b). split.
      * by apply kb_gamma_set_free_bit.
      * apply testbit_over_setbit_same.
  - (** Soundness: { testbit v i | v ∈ γ kb } ⊆ γ[qv](kb_testbit kb i) *)
    move=> b [v [Hv Heq]]. subst. exact (Hv i).
Qed.

(** ExactOrder for non-bottom known-bits: follows from kb_testbit
    being exact at every bit position. *)
Instance nbkb_exact_order : ExactOrder nbkb.
Proof.
  move=> [a2 P2] [a1 P1]. split.
  - apply sound_order.
  - rewrite /(_ ⊑γ[nbkb] _) /(_ ⊑[nbkb] _) //=.
    move=> Hsub i.
    rewrite qv_sqsubseteq_exact. unfold_set => b Hb.
    have [v [Hv Hvi]] := (proj1 (kb_testbit_exact (exist _ a2 P2) i)) b Hb.
    have := Hsub v Hv. unfold_set. move /(_ i). by rewrite Hvi.
Qed.

(** ** Gamma-injectivity for non-bottom known-bits *)

(** Non-bottom qv values have antisymmetric ordering. *)
Lemma qv_non_bottom_antisymm (q1 q2 : quadrivalent) :
  q1 <> QBottom -> q2 <> QBottom ->
  q1 ⊑ q2 -> q2 ⊑ q1 -> q1 = q2.
Proof. by destruct q1, q2. Qed.

(** Abstract equivalence on non-bottom known-bits implies structural equality. *)
Lemma nbkb_equiv_eq (kb1 kb2 : nb_must0_must1) :
  kb1 ⊑⊒[nbkb] kb2 -> `kb1 = `kb2.
Proof.
  move=> [Hord1 Hord2].
  destruct kb1 as [kb1 Hnb1], kb2 as [kb2 Hnb2]. simpl in *.
  apply kb_testbit_ext => i.
  apply qv_non_bottom_antisymm; [exact (Hnb1 i) | exact (Hnb2 i) | exact (Hord1 i) | exact (Hord2 i)].
Qed.

(** Non-bottom known-bits have injective gamma. *)
Lemma nbkb_gamma_injective (kb1 kb2 : nb_must0_must1) :
  γ[nbkb] kb1 ⊆⊇ γ[nbkb] kb2 -> `kb1 = `kb2.
Proof.
  move=> Hgamma. apply nbkb_equiv_eq. exact (is_gamma_injective kb1 kb2 Hgamma).
Qed.

(** ** α-characterization (sufficient direction)

   A non-bottom [kb] is the α of [S] whenever, at every bit position,
   [kb_testbit kb i] is the quadrivalent α of [{testbit v i | v ∈ S}].
   The reverse direction needs classical reasoning (extracting a
   per-bit existential from minimality is Markov-style), but this
   direction is what we use to package transfer functions as α. *)
Lemma kb_is_alpha_of_perbit (a : nb_must0_must1) (S : propset Z) :
  (forall i, ExactlyRepresents (A := qv_abs)
              (kb_testbit (`a) i)
              (collecting_forward (fun v => testbit v i) S))
  -> IsAlpha (A := kb_ad) (`a) S.
Proof.
  move: a => [kb Hnb] /=.
  move=> Hper a'. split.
  - (** [S ⊆ γ a' → kb ⊑ a'] *)
    move=> HSa' i. rewrite qv_sqsubseteq_exact. unfold_set => b Hb.
    have [Hsub _] := Hper i.
    have Hex : b ∈ collecting_forward (fun v => testbit v i) S by apply Hsub.
    move: Hex. unfold_set => [[v [Hv Hbv]]]. subst.
    have := HSa' v Hv. by move /(_ i); unfold_set.
  - (** [kb ⊑ a' → S ⊆ γ a'] *)
    move=> Hkba' v Hv j. unfold_set.
    have [_ Hsup] := Hper j.
    have Hb_qv : testbit v j ∈ γ[qv_abs] (kb_testbit kb j).
    { apply Hsup. unfold_set. by exists v. }
    have := Hkba' j. rewrite qv_sqsubseteq_exact. unfold_set.
    by apply.
Qed.
