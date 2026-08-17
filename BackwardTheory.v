(* BackwardTheory.v - What the backward (refinement) interface of
   [Backward.v] promises, and the proof that the packaging there delivers it.
   Proofs only; nothing here is extracted, which is why it may mention the
   [abstraction] / [abstract_domain] records that [Backward.v] must not.

   The specification is parameterised by the precision relation, exactly as
   [unary_spec] / [binary_spec] / [ternary_spec] are ([Abstraction.v]), so
   soundness and optimality are two instances of one statement rather than
   two interfaces. *)

Require Import Abstraction AbstractLattice AbstractionCombination Backward.
Require Import ssreflect ssrbool ssrfun.
Require Import base.

(* As in [Abstraction.v]: the domain binders below are written
   [`{A : abstract_domain C}] and leave [C] to be generalized. *)
Generalizable All Variables.

(** * One operand's answer.

    [None] claims the incoming operand already is [rel] of the backward set;
    [Some a'] claims the refinement is, and that it is a *strict* refinement
    of the previous value : this lets an analyzer treat [Some] as progress. *)
Definition operand_spec `{A : abstract_domain C} `{Equiv A}
  (rel : A -> ℘ C -> Prop) (o : option A) (a : A) (S : ℘ C) : Prop :=
  match o with
  | None => rel a S
  | Some a' => rel a' S /\ a' ⊑[A] a /\ a' ≢ a
  end.

(** Weakening the precision claim about one operand (e.g. best -> sound). *)
Lemma operand_spec_weaken `{A : abstract_domain C} `{Equiv A}
  (rel rel' : A -> ℘ C -> Prop) o a S :
  (forall x T, rel x T -> rel' x T) -> operand_spec rel o a S -> operand_spec rel' o a S.
Proof.
  move=> Hw. case: o => [b|] /=; last exact: Hw.
  by move=> [Hr Hrest]; split; first exact: Hw.
Qed.

(** * The unary specification.

    There is one projection, so "the two are empty together" is vacuous and
    [Bot] simply reports that projection empty. *)
Section UnarySpec.
  Context `{A1 : abstract_domain C1} `{A0 : abstraction C0} `{Equiv A1}.

  Definition unary_spec (rel1 : A1 -> ℘ C1 -> Prop)
    (F : setop2 C1 C0 C1) (f' : A1 -> A0 -> unary_result A1) : Prop :=
    forall a1 a0,
      match f' a1 a0 with
      | WithBottom.Bot => F (γ[A1] a1) (γ[A0] a0) ⊆⊇ ∅
      | WithBottom.NotBot o1 => operand_spec rel1 o1 a1 (F (γ[A1] a1) (γ[A0] a0))
      end.

  Definition unary_overapproximation := unary_spec Overapproximates.
  Definition unary_most_precise := unary_spec MostPrecise.
  Definition unary_exact := unary_spec ExactlyRepresents.

  Lemma unary_spec_weaken (rel rel' : A1 -> ℘ C1 -> Prop) F f' :
    (forall a S, rel a S -> rel' a S) -> unary_spec rel F f' -> unary_spec rel' F f'.
  Proof.
    move=> Hw Hs a1 a0. move: (Hs a1 a0).
    case: (f' a1 a0) => [|o1] //=. exact: operand_spec_weaken.
  Qed.

  Lemma unary_exact_overapproximation F f' :
    unary_exact F f' -> unary_overapproximation F f'.
  Proof.
    apply: unary_spec_weaken => a S Hx; exact: Exactly_represents_overapproximates.
  Qed.

  Lemma unary_most_precise_overapproximation F f' :
    unary_most_precise F f' -> unary_overapproximation F f'.
  Proof. by apply: unary_spec_weaken => a S []. Qed.
End UnarySpec.
  
(** * The binary specification. *)

Section BinarySpec.
  Context `{A2 : abstract_domain C2} `{A1 : abstract_domain C1}
          `{A0 : abstraction C0} `{Equiv A2} `{Equiv A1}.

  Definition binary_spec (rel2 : A2 -> ℘ C2 -> Prop) (rel1 : A1 -> ℘ C1 -> Prop)
    (FL : setop3 C2 C1 C0 C2) (FR : setop3 C2 C1 C0 C1)
    (f' : A2 -> A1 -> A0 -> binary_result A2 A1) : Prop :=
    forall a2 a1 a0,
      match f' a2 a1 a0 with
      | WithBottom.Bot =>
          FL (γ[A2] a2) (γ[A1] a1) (γ[A0] a0) ⊆⊇ ∅ /\
          FR (γ[A2] a2) (γ[A1] a1) (γ[A0] a0) ⊆⊇ ∅
      | WithBottom.NotBot (o2, o1) =>
          operand_spec rel2 o2 a2 (FL (γ[A2] a2) (γ[A1] a1) (γ[A0] a0)) /\
          operand_spec rel1 o1 a1 (FR (γ[A2] a2) (γ[A1] a1) (γ[A0] a0))
      end.

  Definition binary_overapproximation := binary_spec Overapproximates Overapproximates.
  Definition binary_most_precise := binary_spec MostPrecise MostPrecise.
  Definition binary_exact := binary_spec ExactlyRepresents ExactlyRepresents.


  Lemma binary_spec_weaken
    (rel2 rel2' : A2 -> ℘ C2 -> Prop) (rel1 rel1' : A1 -> ℘ C1 -> Prop)
    FL FR f' :
    (forall a S, rel2 a S -> rel2' a S) -> (forall a S, rel1 a S -> rel1' a S) ->
    binary_spec rel2 rel1 FL FR f' -> binary_spec rel2' rel1' FL FR f'.
  Proof.
    move=> H2 H1 Hs a2 a1 a0. move: (Hs a2 a1 a0).
    case: (f' a2 a1 a0) => [|[o2 o1]] //= [Hl Hr].
    by split; [apply: (operand_spec_weaken _ _ _ _ _ H2 Hl)
              | apply: (operand_spec_weaken _ _ _ _ _ H1 Hr)].
  Qed.

  Lemma binary_exact_overapproximation FL FR f' :
    binary_exact FL FR f' -> binary_overapproximation FL FR f'.
  Proof.
    apply: binary_spec_weaken => a S Hx; exact: Exactly_represents_overapproximates.
  Qed.

  Lemma binary_most_precise_overapproximation FL FR f' :
    binary_most_precise FL FR f' -> binary_overapproximation FL FR f'.
  Proof. by apply: binary_spec_weaken => a S []. Qed.
End BinarySpec.



(** An over-approximation of a set that concretises to ∅ forces the set to be
    ∅. This is the whole content of the [Bot] branch. *)
Lemma empty_of_over `{R : abstract_domain C} (r : R) (S : ℘ C) :
  Overapproximates (A:=R) r S -> γ[R] r ⊆⊇ ∅ -> S ⊆⊇ ∅.
Proof.
  move=> Hover Hemp. rewrite propset_equiv_empty_iff => -[c Hc].
  exact: (proj1 (propset_elem_of_empty c) (proj1 Hemp c (Hover c Hc))).
Qed.

(** …and [Bot] needs no more than that, so the two stronger precisions reach
    it through their own [Overapproximates] component. *)
Lemma most_precise_over `{R : abstract_domain C} (r : R) (S : ℘ C) :
  MostPrecise r S -> Overapproximates r S.
Proof. by case. Qed.

Lemma exact_over `{R : abstract_domain C} (r : R) (S : ℘ C) :
  ExactlyRepresents r S -> Overapproximates r S.
Proof. by move=> Hx; apply: Exactly_represents_overapproximates. Qed.

(** * One operand's answer is correct.

    The [NotBot] branch of both packagings is this lemma, applied once per
    operand: given that the raw refinement [r] of [a] is non-empty — [b] is
    [r] seen as such — and that [r] is [relR] of that operand's backward set,
    the [option] that [refinement] builds satisfies [operand_spec].

    Nothing in it is binary, which is the point: the binary packaging is not
    twice the unary one, it is the unary one twice plus the [Bot] argument
    that couples the two sides. *)

Section OperandCorrect.
  Context `{R : abstract_domain C} (P : R -> Prop).
  Local Notation A := (Subset.ad R P).
  Context `{Equiv A}.
  Hypothesis HE : forall a b : A, a ≡ b <-> `a = `b.
  Variable eqb : R -> R -> bool.
  Hypothesis Heqb : forall r r', reflect (r = r') (eqb r r').

  Lemma refinement_spec (relR : R -> ℘ C -> Prop) (relA : A -> ℘ C -> Prop)
    (Hup : forall (b : A) S, relR (`b) S -> relA b S)
    {a b : A} {r : R} {S : ℘ C} :
    `b = r -> r ⊑[R] `a -> relR r S ->
    operand_spec relA (refinement (@proj1_sig _ _) eqb a r b) a S.
  Proof using HE Heqb.
    move=> Hb Hle Hrel. rewrite /refinement.
    case: (Heqb r (`a)) => [Heq|Hne] /=.
    - apply: Hup. by rewrite -Heq.
    - have Hne' : `b <> `a by rewrite Hb.
      split; first by apply: Hup; rewrite Hb.
      split; first by apply: Subset.Transport.le; rewrite Hb; exact: Hle.
      by move=> /HE Habs; apply: Hne'.
  Qed.
End OperandCorrect.

(** * Correctness of the packaging, once and for all.

    The only real inputs are: the raw functions are sound at the chosen
    precision [relR], they refine (never grow) their operand, and the two
    backward sets are empty together. *)

Section PackagingBinary.
  Context `{R2 : abstract_domain C2} `{R1 : abstract_domain C1}
          `{A0 : abstraction C0}.
  Variables (P2 : R2 -> Prop) (P1 : R1 -> Prop).
  Local Notation A2 := (Subset.ad R2 P2).
  Local Notation A1 := (Subset.ad R1 P1).
  Context `{Equiv A2} `{Equiv A1}.

  (** Equivalence on the operands is equality of the underlying elements:
      the proof component is never looked at. *)
  Hypothesis HE2 : forall a b : A2, a ≡ b <-> `a = `b.
  Hypothesis HE1 : forall a b : A1, a ≡ b <-> `a = `b.

  Variables (to_non_empty2 : R2 -> option A2) (to_non_empty1 : R1 -> option A1).
  Hypothesis to_non_empty2P :
    forall r, if to_non_empty2 r is Some b then `b = r else γ[R2] r ⊆⊇ ∅.
  Hypothesis to_non_empty1P :
    forall r, if to_non_empty1 r is Some b then `b = r else γ[R1] r ⊆⊇ ∅.

  Variables (eqb2 : R2 -> R2 -> bool) (eqb1 : R1 -> R1 -> bool).
  Hypothesis Heqb2 : forall r r', reflect (r = r') (eqb2 r r').
  Hypothesis Heqb1 : forall r r', reflect (r = r') (eqb1 r r').

  Variables (bleft : A2 -> A1 -> A0 -> R2) (bright : A2 -> A1 -> A0 -> R1).
  Hypothesis Hle2 : forall a2 a1 a0, bleft a2 a1 a0 ⊑[R2] `a2.
  Hypothesis Hle1 : forall a2 a1 a0, bright a2 a1 a0 ⊑[R1] `a1.

  Variables (FL : setop3 C2 C1 C0 C2) (FR : setop3 C2 C1 C0 C1).
  Hypothesis Hempty : forall S2 S1 S0, FL S2 S1 S0 ⊆⊇ ∅ <-> FR S2 S1 S0 ⊆⊇ ∅.

  Local Notation pack :=
    (fun a2 a1 a0 =>
       hoist_binary to_non_empty2 (@proj1_sig _ _) eqb2
                    to_non_empty1 (@proj1_sig _ _) eqb1
         a2 a1 (bleft a2 a1 a0) (bright a2 a1 a0)).

  Theorem hoist_binary_spec
    (relR2 : R2 -> ℘ C2 -> Prop) (relA2 : A2 -> ℘ C2 -> Prop)
    (relR1 : R1 -> ℘ C1 -> Prop) (relA1 : A1 -> ℘ C1 -> Prop) :
    (forall (b : A2) S, relR2 (`b) S -> relA2 b S) ->
    (forall (b : A1) S, relR1 (`b) S -> relA1 b S) ->
    (forall (r : R2) S, relR2 r S -> Overapproximates (A:=R2) r S) ->
    (forall (r : R1) S, relR1 r S -> Overapproximates (A:=R1) r S) ->
    ternary_spec A2 A1 A0 R2 bleft FL relR2 ->
    ternary_spec A2 A1 A0 R1 bright FR relR1 ->
    binary_spec relA2 relA1 FL FR pack.
  Proof using HE1 HE2 Hempty Heqb1 Heqb2 Hle1 Hle2 to_non_empty1P to_non_empty2P.
    move=> Hup2 Hup1 Hov2 Hov1 Hsl Hsr a2 a1 a0.
    have HL := Hsl a2 a1 a0. have HR := Hsr a2 a1 a0.
    rewrite /binary_spec /hoist_binary.
    move: (to_non_empty2P (bleft a2 a1 a0)) (to_non_empty1P (bright a2 a1 a0)).
    case: (to_non_empty2 (bleft a2 a1 a0)) => [b2|];
      case: (to_non_empty1 (bright a2 a1 a0)) => [b1|] /= H2 H1.
    (* Both sides non-empty: [refinement_spec], once per operand. *)
    - split.
      + exact: (refinement_spec P2 HE2 eqb2 Heqb2 _ _ Hup2 H2 (Hle2 _ _ _) HL).
      + exact: (refinement_spec P1 HE1 eqb1 Heqb1 _ _ Hup1 H1 (Hle1 _ _ _) HR).
    (* One side empty, or both: either report is reliable, and [Hempty]
       carries it to the other operand. *)
    - have HRe := empty_of_over _ _ (Hov1 _ _ HR) H1.
      by split; [exact: (proj2 (Hempty _ _ _) HRe) | exact: HRe].
    - have HLe := empty_of_over _ _ (Hov2 _ _ HL) H2.
      by split; [exact: HLe | exact: (proj1 (Hempty _ _ _) HLe)].
    - split.
      + exact: (empty_of_over _ _ (Hov2 _ _ HL) H2).
      + exact: (empty_of_over _ _ (Hov1 _ _ HR) H1).
  Qed.

  (** The three instances. [relR] occurs only in the hypotheses, never in the
      conclusion, so each of them pins it down by naming the transfer lemmas
      rather than leaving it to unification. *)

  Corollary hoist_binary_overapproximation :
    ternary_overapproximation A2 A1 A0 R2 bleft FL ->
    ternary_overapproximation A2 A1 A0 R1 bright FR ->
    binary_overapproximation FL FR pack.
  Proof using HE1 HE2 Hempty Heqb1 Heqb2 Hle1 Hle2 to_non_empty1P to_non_empty2P.
    apply: (hoist_binary_spec _ _ _ _ (Subset.Transport.over P2) (Subset.Transport.over P1)
              (fun _ _ Hx => Hx) (fun _ _ Hx => Hx)).
  Qed.

  Corollary hoist_binary_most_precise :
    ternary_best A2 A1 A0 R2 bleft FL ->
    ternary_best A2 A1 A0 R1 bright FR ->
    binary_most_precise FL FR pack.
  Proof using HE1 HE2 Hempty Heqb1 Heqb2 Hle1 Hle2 to_non_empty1P to_non_empty2P.
    apply: (hoist_binary_spec _ _ _ _ (Subset.Transport.most_precise P2) (Subset.Transport.most_precise P1)
              most_precise_over most_precise_over).
  Qed.

  Corollary hoist_binary_exact :
    ternary_exact A2 A1 A0 R2 bleft FL ->
    ternary_exact A2 A1 A0 R1 bright FR ->
    binary_exact FL FR pack.
  Proof using HE1 HE2 Hempty Heqb1 Heqb2 Hle1 Hle2 to_non_empty1P to_non_empty2P.
    apply: (hoist_binary_spec _ _ _ _ (Subset.Transport.exact P2) (Subset.Transport.exact P1)
              exact_over exact_over).
  Qed.
End PackagingBinary.

(** The unary case, the same way and shorter: one projection, so [Bot] simply
    reports it empty and no "empty together" argument is needed. *)
Section PackagingUnary.
  Context `{R1 : abstract_domain C1} `{A0 : abstraction C0}.
  Variable P1 : R1 -> Prop.
  Local Notation A1 := (Subset.ad R1 P1).
  Context `{Equiv A1}.

  Hypothesis HE1 : forall a b : A1, a ≡ b <-> `a = `b.
  Variable to_non_empty1 : R1 -> option A1.
  Hypothesis to_non_empty1P :
    forall r, if to_non_empty1 r is Some b then `b = r else γ[R1] r ⊆⊇ ∅.
  Variable eqb1 : R1 -> R1 -> bool.
  Hypothesis Heqb1 : forall r r', reflect (r = r') (eqb1 r r').
  Variable bfun : A1 -> A0 -> R1.
  Hypothesis Hle1 : forall a1 a0, bfun a1 a0 ⊑[R1] `a1.
  Variable F : setop2 C1 C0 C1.

  Local Notation pack1 :=
    (fun a1 a0 => hoist_unary to_non_empty1 (@proj1_sig _ _) eqb1 a1 (bfun a1 a0)).

  Theorem hoist_unary_spec
    (relR1 : R1 -> ℘ C1 -> Prop) (relA1 : A1 -> ℘ C1 -> Prop) :
    (forall (b : A1) S, relR1 (`b) S -> relA1 b S) ->
    (forall (r : R1) S, relR1 r S -> Overapproximates (A:=R1) r S) ->
    (forall a1 a0, relR1 (bfun a1 a0) (F (γ[A1] a1) (γ[A0] a0))) ->
    unary_spec relA1 F pack1.
  Proof using HE1 Heqb1 Hle1 to_non_empty1P.
    move=> Hup Hov Hs a1 a0.
    have HS := Hs a1 a0.
    rewrite /unary_spec /hoist_unary.
    move: (to_non_empty1P (bfun a1 a0)).
    case: (to_non_empty1 (bfun a1 a0)) => [b1|] /= H1.
    - exact: (refinement_spec P1 HE1 eqb1 Heqb1 _ _ Hup H1 (Hle1 _ _) HS).
    - exact: (empty_of_over _ _ (Hov _ _ HS) H1).
  Qed.

  Corollary hoist_unary_overapproximation :
    (forall a1 a0, Overapproximates (A:=R1) (bfun a1 a0)
                     (F (γ[A1] a1) (γ[A0] a0))) ->
    unary_overapproximation F pack1.
  Proof using HE1 Heqb1 Hle1 to_non_empty1P.
    apply: (hoist_unary_spec _ _ (Subset.Transport.over P1) (fun _ _ Hx => Hx)).
  Qed.

  Corollary hoist_unary_exact :
    (forall a1 a0, ExactlyRepresents (A:=R1) (bfun a1 a0)
                     (F (γ[A1] a1) (γ[A0] a0))) ->
    unary_exact F pack1.
  Proof using HE1 Heqb1 Hle1 to_non_empty1P.
    apply: (hoist_unary_spec _ _ (Subset.Transport.exact P1) exact_over).
  Qed.

  Corollary hoist_unary_most_precise :
    (forall a1 a0, MostPrecise (A:=R1) (bfun a1 a0)
                     (F (γ[A1] a1) (γ[A0] a0))) ->
    unary_most_precise F pack1.
  Proof using HE1 Heqb1 Hle1 to_non_empty1P.
    apply: (hoist_unary_spec _ _ (Subset.Transport.most_precise P1) most_precise_over).
  Qed.
End PackagingUnary.
