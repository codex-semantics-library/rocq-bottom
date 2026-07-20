(* KnownBits.v - Known-bits abstraction for Z using must0_must1 representation *)

Require Import Abstraction.
Require Import autoreflect.
Require Import Quadrivalent.
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
  Local Definition setbit_to (v : Z) (i : nat) (b : bool) : Z :=
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
