(* QuotTheory.v - [Z.quot] (truncating division) transfer function for the
   ZInterval single-value abstraction: [interval_quot] on two intervals.
   Split out of Z_interval.v. *)

(* STATUS: quot (Z.quot): best in all 9 sign cases
     (interval_quot_*_best, interval_quot_full_best).
   Dispatches on [classify] / [classify_divisor], still in ZIntervalTheory.v, and
   uses the negation transfer function ([neg_bound], [interval_opp]), now in
   [OpsComp.v]. *)

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
Require Import Transfer_function.ZInterval.OppTheory.
Open Scope Z_scope.
Generalizable All Variables.

Section Interval_quot.

  (** * Collecting semantics for quotient: excludes division by zero.
      The result is empty (bottom) when all divisors are zero. *)
  Definition collecting_quot (S2 S1 : propset Z) : propset Z :=
    {[c0 | exists c2 c1, c2 ∈ S2 /\ c1 ∈ S1 /\ c1 <> 0 /\ Z.quot c2 c1 = c0]}.
  Hint Unfold collecting_quot: to_set.

  
  Section Interval_quot_pos.
    
    (** Soundness for non-negative dividend / strictly positive divisor.
      The hypotheses constrain the abstract intervals, which rules out
      impossible bound configurations (e.g. Top lower bounds). *)
    Lemma interval_quot_pos_sound l2 h2 l1 h1:
      0 <= l2 -> 0 < l1 ->
      Overapproximates (A:=itv) (interval_quot_pos (WithTop.NotTop l2,h2) (WithTop.NotTop l1,h1))
        (collecting_binary_forward Z.quot (γ[itv] (WithTop.NotTop l2,h2)) (γ[itv] (WithTop.NotTop l1,h1))).
    Proof.
      move=> Ha2pos Ha1pos c0 Hc0.
      unfold_set in Hc0. simpl in Hc0.
      move: Hc0 => [c2 [c1 [Hc2 [Hc1 Hc0]]]]. subst c0.
      move: h1 h2 Ha2pos Ha1pos Hc2 Hc1 => [|h1] [|h2]
                                            Ha2pos Ha1pos Hc2 Hc1;
                                          simpl in *; unfold_set in Hc2; unfold_set in Hc1; unfold_set;
                                          simpl in *; try done.
      all: repeat split.
      all: try (apply Z.quot_pos; lia).
      all: try (transitivity (c2 ÷ l1); [apply Z.quot_le_compat_l|apply Z.quot_le_mono]; lia).
      all: try (transitivity (l2 ÷ c1); [apply Z.quot_le_compat_l|apply Z.quot_le_mono]; lia).
    Qed.

    (** Division is not exact on itv: the result interval may contain
      elements not realizable as c2/c1 for any c2, c1 in the inputs.
      Counterexample: [4,4] / [1,2] = [2,4], but 3 ∉ {4/1, 4/2} = {4, 2}. *)
    Example interval_quot_not_exact:
      ~ (binary_exact itv itv itv interval_quot_pos (collecting_binary_forward Z.quot)).
    Proof.
      set a2 := (WithTop.NotTop 4, WithTop.NotTop 4) : interval.
      set a1 := (WithTop.NotTop 1, WithTop.NotTop 2) : interval.
      set k := 3.
      assert (Hk_in_result: k ∈ γ[itv] (interval_quot_pos a2 a1))
        by solve_with_autoreflect.
      move /(_ a2 a1). to_set.
      have HU := unfold_set_equiv. unfold_set.
      move /(_ k). unfold γ.
      move=> H. apply H in Hk_in_result.
      unfold_set in Hk_in_result.
      move: Hk_in_result => [c2 [c1 [Hc2 [Hc1 Hk]]]].
      simpl in *. unfold_set in Hc2. unfold_set in Hc1.
      (* c2 = 4, c1 ∈ {1, 2}, and 4/c1 = 3 is impossible *)
      have Hc2v: c2 = 4 by lia.
      have Hc1v: c1 = 1 \/ c1 = 2 by lia.
      subst c2 k. destruct Hc1v as [-> | ->]; vm_compute in Hk; lia.
    Qed.

    
    (** Non-bottom preservation for division under positivity. *)
    Lemma interval_quot_preserves_non_bottom l2 h2 l1 h1:
      0 <= l2 -> 0 < l1 ->
      non_bottom (WithTop.NotTop l2, h2) ->
      non_bottom (WithTop.NotTop l1, h1) ->
      non_bottom (interval_quot_pos (WithTop.NotTop l2, h2) (WithTop.NotTop l1, h1)).
    Proof.
      move=> Hl2 Hl1 Hnb2 Hnb1.
      apply non_bottom_non_empty.
      have /non_bottom_non_empty [c2 Hc2] := Hnb2.
      have /non_bottom_non_empty [c1 Hc1] := Hnb1.
      exists (Z.quot c2 c1).
      apply (interval_quot_pos_sound l2 h2 l1 h1 Hl2 Hl1).
      unfold_set. exists c2, c1.
      unfold_set in Hc2. unfold_set in Hc1.
      repeat split; tauto.
    Qed.

    (** Lift interval_quot to nb_interval under positivity hypotheses. *)
    Definition nb_interval_quot
      (a2 a1 : nb_interval) (l2 l1 : Z)
      (Heq2 : fst (`a2) = WithTop.NotTop l2)
      (Heq1 : fst (`a1) = WithTop.NotTop l1)
      (Hl2 : 0 <= l2) (Hl1 : 0 < l1)
      : nb_interval.
    Proof.
      refine (exist _ (interval_quot_pos (`a2) (`a1)) _).
      abstract (
          move: a2 a1 Heq2 Heq1 => [[l2' h2] P2] [[l1' h1] P1] /= Heq2 Heq1;
                                  subst l2' l1';
                                  exact (interval_quot_preserves_non_bottom l2 h2 l1 h1 Hl2 Hl1 P2 P1)
        ).
    Defined.

    (** Soundness at the nbitv level: the result (at the itv level) overapproximates
      the collecting semantics of the nbitv inputs. *)
    Lemma nb_interval_quot_pos_sound (a2 a1 : nb_interval) l2 l1:
      fst (`a2) = WithTop.NotTop l2 ->
      fst (`a1) = WithTop.NotTop l1 ->
      0 <= l2 -> 0 < l1 ->
      Overapproximates (A:=itv) (interval_quot_pos (`a2) (`a1))
        (collecting_binary_forward Z.quot (γ[nbitv] a2) (γ[nbitv] a1)).
    Proof.
      move=> Ha2 Ha1 Hl2 Hl1 c0 Hc0.
      unfold_set in Hc0. move: Hc0 => [c2 [c1 [Hc2 [Hc1 Hc0]]]]. subst c0.
      rewrite !gamma_nbitv_gamma_itv in Hc2, Hc1.
      move: a2 a1 Ha2 Ha1 Hc2 Hc1 => [[l2' h2] P2] [[l1' h1] P1] /= Ha2 Ha1 Hc2 Hc1.
      subst l2' l1'.
      apply (interval_quot_pos_sound l2 h2 l1 h1 Hl2 Hl1).
      unfold_set. by exists c2, c1.
    Qed.

    (** ** Completeness for constant divisor.
      When dividing [l,h] by a constant d > 0, every element of the
      result interval [l/d, h/d] is realized as c/d for some c in [l,h]. *)

    Lemma interval_quot_const_complete l2 h2 (d : Z):
      0 <= l2 -> 0 < d ->
      non_bottom (WithTop.NotTop l2, h2) ->
      forall k, k ∈ γ[itv] (interval_quot_pos (WithTop.NotTop l2, h2)
                         (WithTop.NotTop d, WithTop.NotTop d)) ->
           k ∈ collecting_binary_forward Z.quot
             (γ[itv] (WithTop.NotTop l2, h2))
             (γ[itv] (WithTop.NotTop d, WithTop.NotTop d)).
    Proof.
      move=> Hl2 Hd Hnb k Hk.
      set (c2 := Z.max l2 (k * d)).
      (* Simplify Hk and case split on h2 *)
      move: h2 Hnb Hk => [|h2] Hnb Hk; simpl in Hk; unfold_set in Hk.
      - (* h2 = Top: k ≥ l2/d, no upper bound *)
        unfold_set. exists c2, d.
        have Hwitness: c2 ÷ d = k.
        { subst c2. destruct (Z.max_spec l2 (k * d)) as [[Hlt ->]|[Hge ->]].
          - apply Z.quot_mul; lia.
          - have: k <= l2 ÷ d by (apply Z.quot_le_lower_bound; lia). lia. }
        refine (conj _ (conj _ Hwitness)).
        + simpl. unfold_set. subst c2. lia.
        + simpl. unfold_set. lia.
      - (* h2 = NotTop h2: l2/d ≤ k ≤ h2/d *)
        move: Hk => [Hklo Hkhi].
        have Hlh: l2 <= h2.
        { apply non_bottom_non_empty in Hnb. move: Hnb => [c' Hc'].
          simpl in Hc'. unfold_set in Hc'. lia. }
        unfold_set. exists c2, d.
        have Hwitness: c2 ÷ d = k.
        { subst c2. destruct (Z.max_spec l2 (k * d)) as [[Hlt ->]|[Hge ->]].
          - apply Z.quot_mul; lia.
          - have: k <= l2 ÷ d by (apply Z.quot_le_lower_bound; lia). lia. }
        refine (conj _ (conj _ Hwitness)).
        + simpl. unfold_set. subst c2. split; [lia |].
          destruct (Z.max_spec l2 (k * d)) as [[Hlt ->]|[Hge ->]].
          * have: k * d <= (h2 ÷ d) * d by nia.
            have: (h2 ÷ d) * d <= h2 by (rewrite Z.mul_comm; apply Z.mul_quot_le; lia).
            lia.
          * have: d * (l2 ÷ d) <= l2 by (apply Z.mul_quot_le; lia).
            lia.
        + simpl. unfold_set. lia.
    Qed.

    (** ** Best abstraction for positive quotient. *)

    (** Local abbreviation: the collecting quotient set for the
        positive-divisor case (both lower bounds finite). Just
        [collecting_quot] with the interval-γ wrapping factored out, so
        the three bound lemmas below need not repeat it. *)
    Let pos_quot l2 h2 l1 h1 :=
      collecting_quot
        (γ[itv] (WithTop.NotTop l2, h2))
        (γ[itv] (WithTop.NotTop l1, h1)).

    (** The lower bound [quot_bound (NotTop l2) h1] is the GLB of the quotient set.
        Since l2 is finite, this is always [NotTop _], so we're in the [is_glb] case. *)
    Lemma interval_quot_pos_glb l2 h2 l1 h1 :
      0 <= l2 -> 0 < l1 ->
      non_bottom (WithTop.NotTop l2, h2) ->
      non_bottom (WithTop.NotTop l1, h1) ->
      GLBUnbounded.is_α Z.le (quot_bound (WithTop.NotTop l2) h1) (pos_quot l2 h2 l1 h1).
    Proof.
      move=> Hl2 Hl1 Hnb2 Hnb1.
      have Hl2in: l2 ∈ γ[itv] (WithTop.NotTop l2, h2).
      { destruct h2 as [|h2']; unfold_set; simpl in Hnb2; simpl; lia. }      
      case: h1 Hnb1 => [|h1] Hnb1 /=.
      - (* h1 = Top: GLB is 0 (we can take any value larger than l1. *)
        constructor.
        + (* 0 is a lower bound: c2 ÷ c1 ≥ 0 since c2 ≥ 0, c1 > 0 *)
          move=> z Hz; unfold_set in Hz.
          move: Hz => [c2 [c1 [Hc2 [Hc1 [Hz1 Hz2]]]]]; subst z.
          apply Z.quot_pos; simpl in *; lia.
        + (* 0 is the greatest: witnessed by taking c1 large enough *)
          move=> z Hz. apply (Hz 0).
          unfold_set. exists l2, (Z.max l1 (l2 + 1)).
          refine (conj Hl2in (conj _ _)).
          * simpl. split; [lia | exact I].
          * split.
            -- lia.
            -- apply Z.quot_small; lia.
      - (* h1 = NotTop h1': GLB is l2 ÷ h1'. *)
        have Hlh1: l1 <= h1 by (apply non_bottom_non_empty in Hnb1;
          move: Hnb1 => [c Hc]; simpl in Hc; unfold_set in Hc; simpl in *; lia).
        constructor.
        + (* l2 ÷ h1 is a lower bound *)
          move=> z Hz; unfold_set in Hz.
          move: Hz => [c2 [c1 [Hc2 [Hc1 [Hz1 Hz2]]]]]; subst z.
          unfold_set in Hc2; unfold_set in Hc1; simpl in *.
          transitivity (l2 ÷ c1); [apply Z.quot_le_compat_l|apply Z.quot_le_mono]; lia.
        + (* l2 ÷ h1 is the greatest: witnessed by (l2, h1) *)
          have Hh1in: h1 ∈ γ[itv] (WithTop.NotTop l1, WithTop.NotTop h1).
          { simpl. unfold_set. simpl. split; lia. }
          move=> z Hz; apply Hz; unfold_set; simpl.
          exists l2, h1.
          refine (conj Hl2in (conj Hh1in _)).
          split; [lia|reflexivity].
    Qed.

    (** The upper bound [quot_bound h2 (NotTop l1)] is the best LUB of the quotient set. *)
    Lemma interval_quot_pos_upper l2 h2 l1 h1 :
      0 <= l2 -> 0 < l1 ->
      non_bottom (WithTop.NotTop l2, h2) ->
      non_bottom (WithTop.NotTop l1, h1) ->
      IsAlpha (A:=lubtop)
        (quot_bound h2 (WithTop.NotTop l1))
        (pos_quot l2 h2 l1 h1).
    Proof.
      move=> Hl2 Hl1 Hnb2 Hnb1.
      apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_lubtop)).
      case: h2 Hnb2 => [|h2] Hnb2 /=.
      - (* h2 = Top: quotient set is unbounded *)
        move=> z.
        set c2 := Z.max l2 ((z + 1) * l1).
        exists (c2 ÷ l1). split.
        + unfold_set. exists c2, l1; simpl. repeat split; try lia.
          destruct h1; simpl in Hnb1; unfold_set; lia.
        + subst c2. unfold CRelationClasses.flip.
          have Hmax: Z.max l2 ((z + 1) * l1) >= (z + 1) * l1 by lia.
          apply Z.quot_le_lower_bound; lia.
      - (* h2 = NotTop h2': LUB is h2 ÷ l1 *)
        have Hlh2: l2 <= h2 by (apply non_bottom_non_empty in Hnb2;
          move: Hnb2 => [c Hc]; simpl in Hc; unfold_set in Hc; simpl in *; lia).
        constructor.
        + (* h2 ÷ l1 is an upper bound *)
          move=> z Hz; unfold_set in Hz.
          move: Hz => [c2 [c1 [Hc2 [Hc1 [Hz1 Hz2]]]]]; subst z.
          unfold_set in Hc2; simpl in *.
          move: Hc1 => [Hc1lo Hc1hi].
          transitivity (c2 ÷ l1); [apply Z.quot_le_compat_l|apply Z.quot_le_mono]; lia.
        + (* h2 ÷ l1 is the lowest: witnessed by (h2, l1) *)
          move=> z' Hz'; apply Hz'; unfold_set.
          exists h2, l1; simpl; repeat split; try lia.
          by (destruct h1; simpl; unfold_set).
    Qed.

    (** Combining GLB and LUB: [interval_quot_pos] is the best abstraction. *)
    Lemma interval_quot_pos_best l2 h2 l1 h1 :
      0 <= l2 -> 0 < l1 ->
      non_bottom (WithTop.NotTop l2, h2) ->
      non_bottom (WithTop.NotTop l1, h1) ->
      BestAbstraction (A:=itv)
        (interval_quot_pos (WithTop.NotTop l2, h2) (WithTop.NotTop l1, h1))
        (pos_quot l2 h2 l1 h1).
    Proof.
      move=> Hl2 Hl1 Hnb2 Hnb1.
      apply/AbstractionCombination.Conjunction.best_abstraction_pair_iff; split;
        apply: is_alpha_is_best_abstraction.
      - apply: (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_glbtop)).
        exact: interval_quot_pos_glb.
      - exact: interval_quot_pos_upper.
    Qed.

  End Interval_quot_pos.


  (** * Full interval quotient for all sign combinations.

      Z.quot rounds towards zero, so:
        (-a) ÷ b = -(a ÷ b)
        a ÷ (-b) = -(a ÷ b)
      This lets us reduce to the Pos/Pos case via interval_opp.

      When the divisor crosses zero, we split it into [l1, -1] and
      [1, h1], quot each, and join. When the divisor is exactly {0},
      the collecting set is empty so any interval (including bottom)
      is a sound overapproximation. *)

  (** * Decomposed quotient: one function per sign combination.

      Naming convention: [interval_quot_X_Y] where X is the dividend sign,
      Y is the divisor sign. All reduce to [interval_quot_pos] (pos/pos case)
      via [interval_opp], using the identities:
        (-a) ÷ b = -(a ÷ b)
        a ÷ (-b) = -(a ÷ b)     (Z.quot rounds towards zero) *)


  (** * Inversion lemmas for classify_divisor. *)

  (* Kind of symbolic execution where we split on all integer tests. *)
  Ltac zcases :=
    repeat (repeat (
        case: (Z.gtb_spec _ _) => ? ||
        case: (Z.ltb_spec _ _) => ? ||
        case: (Z.eqb_spec _ _) => ?
      ); simpl in *; try discriminate; try lia).
  
  (** Inversion for [DivPos]: if [classify_divisor i = DivPos i'],
      then the returned interval correspond to the first one with the
      0 removed. *)
  Lemma classify_divisor_pos_inv_alt l h l' h':
    non_bottom (l,h) ->
    classify_divisor (l,h) = DivPos (l',h') ->
    (h' = h) /\
      (exists ll ll', l = WithTop.NotTop ll /\ l' = WithTop.NotTop ll' /\ ll >= 0 /\ ll' > 0) /\
      non_bottom (l',h') /\
      γ[itv] (l',h') ⊆⊇ {[z | z ∈ γ[itv] (l,h) /\ z <> 0]}.
  Proof.
    move => Hnb Hclass.
    have Hhh': h = h'.
    { move: l h Hnb Hclass => [|ll] [|hh] Hnb; zcases; congruence. }
    move: Hhh' Hnb Hclass => <- Hnb Hclass. clear h'.
    split => //.
    have Hexists: (exists ll ll' : Z, l = WithTop.NotTop ll /\ l' = WithTop.NotTop ll' /\ ll >= 0 /\ ll' > 0).
    { move: l h Hnb Hclass => [|ll] [|hh] Hnb; zcases; move => Hclass; injection Hclass => Hl.
      all: try (exists ll,ll; repeat split => //; lia).
      all: (exists 0,1; subst; repeat split; lia). }
    split => //.
    move: Hexists Hnb Hclass => [ll [ll' [-> [-> Hlia]]]] Hnb Hclass. clear l l'.
    split.
    { (* non_bottom (NotTop ll', h) *)
      move: h Hnb Hclass => [|hh] Hnb; zcases;
        move=> Hclass; try discriminate;
        injection Hclass => *; subst; unfold_set; simpl in *; lia. }
    (* (γ[ itv]) (l', h') ⊆⊇ {[ z | z ∈ (γ[ itv]) (l', h') /\ z <> 0 ]} *)
    unfold_set_equiv. move=> z; simpl.
    repeat split => //; try lia; try tauto.
    (* Remains to prove that ll <= z <-> ll' <= z. We need the classify definition for this. *)
    all: move: Hclass; destruct h; zcases; move=> Hclass; try injection Hclass; try lia.
  Qed.

  
  Lemma classify_divisor_neg_inv_alt l h l' h':
    non_bottom (l,h) ->
    classify_divisor (l,h) = DivNeg (l',h') ->
    (l' = l) /\
      (exists hh hh', h = WithTop.NotTop hh /\ h' = WithTop.NotTop hh' /\ hh <= 0 /\ hh' < 0) /\
      non_bottom (l',h') /\
      γ[itv] (l',h') ⊆⊇ {[z | z ∈ γ[itv] (l,h) /\ z <> 0]}.
  Proof.
    move => Hnb Hclass.
    have Hll': l = l'.
    { move: l h Hnb Hclass => [|ll] [|hh] Hnb; zcases; congruence. }
    move: Hll' Hnb Hclass => <- Hnb Hclass. clear l'.
    split => //.
    have Hexists: (exists hh hh' : Z, h = WithTop.NotTop hh /\ h' = WithTop.NotTop hh' /\ hh <= 0 /\ hh' < 0).
    { move: l h Hnb Hclass => [|ll] [|hh] Hnb; zcases; move => Hclass; injection Hclass => Hl.
      all: try (exists hh,hh; repeat split => //; lia).
      all: (exists 0,(-1); subst; repeat split; lia). }
    split => //.
    move: Hexists Hnb Hclass => [hh [hh' [-> [-> Hlia]]]] Hnb Hclass. clear h h'.
    split.
    { (* non_bottom (l, NotTop hh') *)
      move: l Hnb Hclass => [|ll] Hnb; zcases;
        move=> Hclass; try discriminate;
        injection Hclass => *; subst; unfold_set; simpl in *; lia. }
    unfold_set_equiv. move=> z; simpl.
    repeat split => //; try lia; try tauto.
    all: move: Hclass; destruct l; zcases; move=> Hclass; try injection Hclass; try lia.
  Qed.

  (** Inversion for [DivNeg]: if [classify_divisor i = DivNeg i'], then
      the returned interval [i'] has a strictly negative upper bound. *)
  Lemma classify_divisor_neg_inv l h l' h' :
    classify_divisor (l,h) = DivNeg (l',h') ->
    l' = l /\
      (exists hh hh', h = WithTop.NotTop hh /\ h' = WithTop.NotTop hh' /\
                   ((hh < 0 /\ h' = h /\ hh' = hh) \/ (hh = 0 /\ hh' = -1))).
  Proof.
    move: l h => [|ll] [|hh]; zcases; split; try congruence.
    2,4: exists 0, (-1); repeat (split; try right; try congruence; try lia).
    all: exists hh, hh; repeat (split; try left; try congruence; try lia).
  Qed.

  (** Inversion for [DivAcross]: if [classify_divisor i = DivAcross], then
      the interval contains both -1 and 1. *)
  Lemma classify_divisor_across_inv l h :
    classify_divisor (l, h) = DivAcross ->
    (-1) ∈ γ[itv] (l, h) /\ 1 ∈ γ[itv] (l, h).
  Proof.
    move: l h => [|ll] [|hh]; zcases.
    all: unfold_set; simpl; split; lia.
  Qed.

  Hint Unfold collecting_quot: to_set.

  (** Restricting the divisor set to its nonzero elements leaves
      [collecting_quot] unchanged, so any ⊆⊇-equivalence between a
      divisor set and "divisors of S1' distinct from 0" lifts to
      [collecting_quot]. This will still work later when we also take
      into account modulo and known-bits information when we split. *)
  Lemma collecting_quot_restrict_equiv (S2 S1 S1' : propset Z) :
    S1 ⊆⊇ {[z | z ∈ S1' /\ z <> 0]} ->
    collecting_quot S2 S1 ⊆⊇ collecting_quot S2 S1'.
  Proof.
    rewrite propset_equiv_iff => HE.
    unfold_set_equiv => z0.
    apply: exists_iff => c2; apply: exists_iff => c1.
    move: (HE c1); unfold_set; simpl. tauto.
  Qed.

  (** When [classify_divisor i = DivPos i'], the nonzero divisors of [i]
      are exactly the divisors of [i']: the two collecting_quot sets coincide. *)
  (* Lemma classify_divisor_pos_quot i i' : *)
  (*   classify_divisor i = DivPos i' -> *)
  (*   forall S2, collecting_quot S2 (γ[itv] i) ⊆⊇ collecting_quot S2 (γ[itv] i'). *)
  (* Proof. *)
  (*   move: i' => [l' h']. *)
  (*   move: i => [l h] Hcl S2. *)
  (*   unfold_set_equiv. move=> c0. *)
  (*   apply: exists_iff => c2. apply: exists_iff => c1. *)
  (*   move: (classify_divisor_pos_inv _ _ _ _ Hcl) => [-> [ll [ll' [-> [-> [Hinv1 | Hinv2]]]]]]. *)
  (*   - (* ll > 0, l' = l, ll' = ll: both sides are syntactically equal *) *)
  (*     move: Hinv1 => [_ [<- ->]]. tauto. *)
  (*   - (* ll = 0, ll' = 1: 0 ≤ c1 ∧ c1 ≠ 0  ↔  1 ≤ c1 *) *)
  (*     move: Hinv2 => [-> ->]. unfold_set. simpl. intuition lia. *)
  (* Qed. *)

  (** When [classify_divisor i = DivNeg i'], the nonzero divisors of [i]
      are exactly the divisors of [i']. *)
  Lemma classify_divisor_neg_quot i i' :
    classify_divisor i = DivNeg i' ->
    forall S2, collecting_quot S2 (γ[itv] i) ⊆⊇ collecting_quot S2 (γ[itv] i').
  Proof.
    move: i' => [l' h'].
    move: i => [l h] Hcl S2.
    unfold_set_equiv. move=> c0.
    apply: exists_iff => c2. apply: exists_iff => c1.
    move: (classify_divisor_neg_inv _ _ _ _ Hcl) => [-> [hh [hh' [-> [-> [Hinv1 | Hinv2]]]]]].
    - (* hh < 0, h' = h, hh' = hh: both sides equal *)
      move: Hinv1 => [_ [<- ->]]. tauto.
    - (* hh = 0, hh' = -1: c1 ≤ 0 ∧ c1 ≠ 0  ↔  c1 ≤ -1 *)
      move: Hinv2 => [-> ->]. unfold_set. simpl. intuition lia.
  Qed.

  (** When [classify_divisor i = DivZero], the only element of [γ i] is 0,
      so [collecting_quot] is empty — any dividend divided by only-zero is vacuous. *)
  Lemma classify_divisor_zero_empty l h :
    classify_divisor (l, h) = DivZero ->
    forall S2 c, ~ (c ∈ collecting_quot S2 (γ[itv] (l, h))).
  Proof.
    move=> Hcl S2 c [c2 [c1 [_ [Hc1 [Hne _]]]]].
    move: l h Hcl Hc1 => [|ll] [|hh] Hcl Hc1; try (move: Hcl; zcases; done).
    move: Hcl; zcases.
    unfold_set in Hc1; simpl in Hc1; lia.
  Qed.

  (** ** Best abstraction for the other three quarter cases. *)

  (** Helper: the γ of interval_opp is {z | -z ∈ γ(i)}. *)
  Lemma gamma_interval_opp i :
    forall z, z ∈ γ[itv] (interval_opp i) <-> (-z) ∈ γ[itv] i.
  Proof.
    move=> z. have H := interval_opp_exact i. to_set in H.
    have HU := unfold_set_equiv. unfold_set in H. clear HU.
    specialize ( H z). rewrite H. clear H.
    split.
    - move => [c [Hc Hz]]. by replace (-z) with c by lia.
    - move => Hz. exists (-z). split; [done|lia].
  Qed.

  Lemma interval_quot_neg_pos_best l2 h2 l1 h1 :
    h2 <= 0 -> 0 < l1 ->
    non_bottom (l2, WithTop.NotTop h2) ->
    non_bottom (WithTop.NotTop l1, h1) ->
    BestAbstraction (A:=itv)
      (interval_quot_neg_pos (l2, WithTop.NotTop h2) (WithTop.NotTop l1, h1))
      (collecting_quot
        (γ[itv] (l2, WithTop.NotTop h2))
        (γ[itv] (WithTop.NotTop l1, h1))).
  Proof.
    move=> Hh2 Hl1 Hnb2 Hnb1.
    have Hnb2' := interval_opp_preserves_non_bottom _ Hnb2.
    simpl in Hnb2'; rewrite /neg_bound in Hnb2'.
    apply (best_abstraction_equiv _ _ _ (best_abstraction_opp _ _
      (interval_quot_pos_best (-h2) (neg_bound l2) l1 h1
         ltac:(lia) Hl1 Hnb2' Hnb1))).
    unfold_set_equiv. simpl. move=>z.
    split; move => [c2 [c1 [[Hc2 Hc2'] [[Hc1 Hc1'] Hz]]]]; exists (-c2), c1; destruct l2; destruct h1; unfold_set in *;
                  (try rewrite Z.quot_opp_l; try lia).
  Qed.

  (** Best abstraction for pos/neg case: dividend ≥ 0, divisor < 0. *)
  Lemma interval_quot_pos_neg_best l2 h2 (l1 : WithTop.with_top Z) h1 :
    0 <= l2 -> h1 < 0 ->
    non_bottom (WithTop.NotTop l2, h2) ->
    non_bottom (l1, WithTop.NotTop h1) ->
    BestAbstraction (A:=itv)
      (interval_quot_pos_neg (WithTop.NotTop l2, h2) (l1, WithTop.NotTop h1))
      (collecting_quot
        (γ[itv] (WithTop.NotTop l2, h2))
        (γ[itv] (l1, WithTop.NotTop h1))).
  Proof.
    move=> Hl2 Hh1 Hnb2 Hnb1.
    have Hnb1' := interval_opp_preserves_non_bottom _ Hnb1.
    simpl in Hnb1'; rewrite /neg_bound in Hnb1'.
    apply (best_abstraction_equiv _ _ _ (best_abstraction_opp _ _
      (interval_quot_pos_best l2 h2 (-h1) (neg_bound l1)
        Hl2 ltac:(lia) Hnb2 Hnb1'))).
    unfold_set_equiv. simpl. move=> z.
    split; move => [c2 [c1 [Hc2 [Hc1 Hz]]]];
      exists c2, (-c1); refine (conj Hc2 (conj _ _));
      destruct l1 as [|l1']; simpl in *;
      (try (unfold_set in Hc1; unfold_set)); try lia;
      rewrite Z.quot_opp_r; try lia.
  Qed.

  (** Best abstraction for neg/neg case: dividend ≤ 0, divisor < 0. *)
  Lemma interval_quot_neg_neg_best l2 h2 l1 h1 :
    h2 <= 0 -> h1 < 0 ->
    non_bottom (l2, WithTop.NotTop h2) ->
    non_bottom (l1, WithTop.NotTop h1) ->
    BestAbstraction (A:=itv)
      (interval_quot_neg_neg (l2, WithTop.NotTop h2) (l1, WithTop.NotTop h1))
      (collecting_quot
        (γ[itv] (l2, WithTop.NotTop h2))
        (γ[itv] (l1, WithTop.NotTop h1))).
  Proof.
    move=> Hh2 Hh1 Hnb2 Hnb1.
    have Hnb2' := interval_opp_preserves_non_bottom _ Hnb2.
    have Hnb1' := interval_opp_preserves_non_bottom _ Hnb1.
    simpl in Hnb2', Hnb1'; rewrite /neg_bound in Hnb2', Hnb1'.
    apply (best_abstraction_equiv _ _ _
      (interval_quot_pos_best (-h2) (neg_bound l2)
         (-h1) (neg_bound l1) ltac:(lia) ltac:(lia) Hnb2' Hnb1')).
    unfold_set_equiv. simpl. move=>z.
    split; move => [c2 [c1 [[Hc2 Hc2'] [[Hc1 Hc1'] Hz]]]]; exists (-c2), (-c1);
                  destruct l1,l2; unfold_set in *;
                  repeat split; (try rewrite Z.quot_opp_opp; try lia).
  Qed.

  (** Splitting the dividend (first arg) of [collecting_quot] at 0. *)
  Lemma collecting_quot_split_dividend
    (l2 h2: WithTop.with_top Z) (S1 : propset Z) z :
    0 ∈ γ[glbtop] l2 ->
    0 ∈ γ[lubtop] h2 ->
    z ∈ collecting_quot (γ[itv] (l2, h2)) S1 <->
    z ∈ (collecting_quot (γ[itv] (l2, WithTop.NotTop 0)) S1 ∪
         collecting_quot (γ[itv] (WithTop.NotTop 0, h2)) S1).
  Proof.
    move=> Hl2 Hh2; unfold_set_equiv; simpl; split.
    - move=> [c2 [c1 [Hc2 [Hc1 [Hne Hz]]]]].
      unfold_set in Hc2; move: Hc2 => [Hc2l Hc2h].
      case: (Z.le_ge_cases c2 0) => Hc2z;
        [left | right]; exists c2, c1; unfold_set;
        repeat split; try assumption; simpl; lia.
    - move=> [[c2 [c1 [Hc2 [Hc1 [Hne Hz]]]]] | [c2 [c1 [Hc2 [Hc1 [Hne Hz]]]]]];
        unfold_set in Hc2; move: Hc2 => [Hc2l Hc2h];
        exists c2, c1; unfold_set; repeat split; try assumption; try done.
      + by case: h2 Hh2 Hc2h => [|?]; unfold_set; simpl in *; lia.
      + by case: l2 Hl2 Hc2l => [|?]; unfold_set; simpl in *; lia.
  Qed.


  (* TODO: this splitting is generic: it should subsume the dividend split used
     for quotient, and be reusable for multiplication. *)
  (** Splitting the first argument of [collecting_binary_forward] at 0. *)
  Lemma collecting_across_split (f: Z -> Z -> Z)
    (l2 h2: WithTop.with_top Z) (S: propset Z) z :
    0 ∈ γ[glbtop] l2 ->
    0 ∈ γ[lubtop] h2 ->
    z ∈ collecting_binary_forward f (γ[itv] (l2, h2)) S <->
    z ∈ (collecting_binary_forward f (γ[itv] (l2, WithTop.NotTop 0)) S ∪
         collecting_binary_forward f (γ[itv] (WithTop.NotTop 0, h2)) S).
  Proof.
    move=> Hl2 Hh2; unfold_set; split.
    - move=> [c2 [c1 [Hc2 [Hc1 Hc0]]]]; unfold_set in Hc2; move: Hc2 => [Hc2l Hc2h].
      case: (Z.le_ge_cases c2 0) => Hc2z;
        [left | right]; exists c2, c1; unfold_set;
        repeat split; try assumption; simpl; lia.
    - move=> [[c2 [c1 [Hc2 [Hc1 Hc0]]]] | [c2 [c1 [Hc2 [Hc1 Hc0]]]]];
        unfold_set in Hc2; move: Hc2 => [Hc2l Hc2h];
        exists c2, c1; unfold_set; repeat split; try assumption.
      + by case: h2 Hh2 Hc2h => [|?]; unfold_set; simpl in *; lia.
      + by case: l2 Hl2 Hc2l => [|?]; unfold_set; simpl in *; lia.
  Qed.

  (** Best abstraction for across/pos case: dividend crosses 0, divisor > 0. *)
  Lemma interval_quot_across_pos_best (l2 : WithTop.with_top Z) (h2 : WithTop.with_top Z)
    (l1 : Z) (h1 : WithTop.with_top Z) :
    0 ∈ γ[glbtop] l2 ->
    0 ∈ γ[lubtop] h2 ->
    0 < l1 ->
    non_bottom (l2, h2) ->
    non_bottom (WithTop.NotTop l1, h1) ->
    BestAbstraction (A:=itv)
      (interval_quot_across_pos  (l2, h2) (WithTop.NotTop l1, h1))
      (collecting_quot
        (γ[itv] (l2, h2))
        (γ[itv] (WithTop.NotTop l1, h1))).
  Proof.
    move=> Hl2 Hh2 Hl1 Hnb2 Hnb1.
    have Hnb2n: non_bottom (l2, WithTop.NotTop 0).
    by case: l2 Hl2 Hnb2 => /= //.
    have Hnb2p: non_bottom (WithTop.NotTop 0, h2)
    by case: h2 Hh2 Hnb2 => /= //.
    have /is_alpha_iff_best_abstraction Hn :=
      interval_quot_neg_pos_best l2 0 l1 h1
        (Z.le_refl 0) Hl1 Hnb2n Hnb1.
    have /is_alpha_iff_best_abstraction Hp :=
      interval_quot_pos_best 0 h2 l1 h1
        (Z.le_refl 0) Hl1 Hnb2p Hnb1.
    apply/is_alpha_iff_best_abstraction.
    apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp).
    apply/propset_equiv_iff => z; exact: (collecting_quot_split_dividend _ _ _ z Hl2 Hh2).
  Qed.

  Lemma interval_quot_across_neg_best (l2 : WithTop.with_top Z) (h2 : WithTop.with_top Z)
    (l1 : WithTop.with_top Z) (h1 : Z) :
    0 ∈ γ[glbtop] l2 ->
    0 ∈ γ[lubtop] h2 ->
    h1 < 0 ->
    non_bottom (l2, h2) ->
    non_bottom (l1, WithTop.NotTop h1) ->
    BestAbstraction (A:=itv)
      (interval_quot_across_neg  (l2, h2) (l1, WithTop.NotTop h1))
      (collecting_quot
        (γ[itv] (l2, h2))
        (γ[itv] (l1, WithTop.NotTop h1))).
  Proof.
    move=> Hl2 Hh2 Hl1 Hnb2 Hnb1.
    have Hnb2n: non_bottom (l2, WithTop.NotTop 0).
    by case: l2 Hl2 Hnb2 => /= //.
    have Hnb2p: non_bottom (WithTop.NotTop 0, h2)
    by case: h2 Hh2 Hnb2 => /= //.
    have /is_alpha_iff_best_abstraction Hn :=
      interval_quot_neg_neg_best l2 0 l1 h1
        (Z.le_refl 0) Hl1 Hnb2n Hnb1.
    have /is_alpha_iff_best_abstraction Hp :=
      interval_quot_pos_neg_best 0 h2 l1 h1
        (Z.le_refl 0) Hl1 Hnb2p Hnb1.
    apply/is_alpha_iff_best_abstraction.
    apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp).
    apply/propset_equiv_iff => z; exact: (collecting_quot_split_dividend _ _ _ z Hl2 Hh2).
  Qed.
  

  (** Splitting the divisor (second arg) of [collecting_quot] at -1/1,
      skipping 0. Every nonzero integer is either ≤ -1 or ≥ 1. *)
  Lemma collecting_quot_split_divisor
    (S2 : propset Z) (l1 h1: WithTop.with_top Z) z :
    0 ∈ γ[glbtop] l1 ->
    0 ∈ γ[lubtop] h1 ->
    z ∈ collecting_quot S2 (γ[itv] (l1, h1)) <->
    z ∈ (collecting_quot S2 (γ[itv] (l1, WithTop.NotTop (-1))) ∪
         collecting_quot S2 (γ[itv] (WithTop.NotTop 1, h1))).
  Proof.
    move=> Hl1 Hh1; unfold_set_equiv; simpl. split.
    - move=> [c2 [c1 [Hc2 [[Hc1l Hc1h] [Hne Hz]]]]].
      case Hc1neg: (Z.leb c1 0); [left|right]; exists c2, c1;
        repeat split; (try done; lia).
    - move=> [[c2 [c1 [Hc2 [[Hc1l Hc1h] [Hz1 Hz2]]]]] | [c2 [c1 [Hc2 [[Hc1l Hc1h] [Hz1 Hz2]]]]]];
        exists c2, c1; repeat split; try done; simpl in *.
      (* left: c1 ∈ γ(l1,-1), widen upper bound and show c1≠0 *)
      + destruct h1; unfold_set; [done | unfold_set in Hh1; lia].
      (* right: c1 ∈ γ(1,h1), widen lower bound and show c1≠0 *)
      + destruct l1; unfold_set; [done | unfold_set in Hl1; lia].
  Qed.

  (** Best abstraction for pos/across case: dividend ≥ 0, divisor crosses 0.
      Uses [collecting_quot] (excludes division by zero). *)
  Lemma interval_quot_pos_across_best (l2 : Z) (h2 : WithTop.with_top Z)
    (l1 h1 : WithTop.with_top Z) :
    0 <= l2 ->
    (-1) ∈ γ[glbtop] l1 ->
    1 ∈ γ[lubtop] h1 ->
    non_bottom (WithTop.NotTop l2, h2) ->
    BestAbstraction (A:=itv)
      (interval_quot_pos_across (WithTop.NotTop l2, h2) (l1, h1))
      (collecting_quot
        (γ[itv] (WithTop.NotTop l2, h2))
        (γ[itv] (l1, h1))).
  Proof.
    move=> Hl2 Hl1 Hh1 Hnb2.
    have Hnb1n: non_bottom (l1, WithTop.NotTop (-1))
      by case: l1 Hl1 => [|?] //; unfold_set; simpl; lia.
    have Hnb1p: non_bottom (WithTop.NotTop 1, h1)
      by case: h1 Hh1 => [|?] //; unfold_set; simpl; lia.
    have Hl1' : 0 ∈ γ[glbtop] l1.
    { destruct l1; [done | unfold_set in Hl1; unfold_set; simpl in *; lia]. }
    have Hh1' : 0 ∈ γ[lubtop] h1.
    { destruct h1; [done | unfold_set in Hh1; unfold_set; simpl in *; lia]. }
    have /is_alpha_iff_best_abstraction Hn :=
      interval_quot_pos_neg_best l2 h2 l1 (-1)
        Hl2 ltac:(lia) Hnb2 Hnb1n.
    have /is_alpha_iff_best_abstraction Hp :=
      interval_quot_pos_best l2 h2 1 h1
        Hl2 ltac:(lia) Hnb2 Hnb1p.
    apply/is_alpha_iff_best_abstraction.
    apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp).
    apply/propset_equiv_iff => z; exact: (collecting_quot_split_divisor _ _ _ z Hl1' Hh1').
  Qed.

  Lemma interval_quot_pos_across_eq l2 h2 l1 h1 :
    0 <= l2 ->
    (-1) ∈ γ[glbtop] l1 ->
    1 ∈ γ[lubtop] h1 ->
    non_bottom (WithTop.NotTop l2, h2) ->
    interval_quot_pos_across_opt (WithTop.NotTop l2, h2) (l1, h1) =
    interval_quot_pos_across (WithTop.NotTop l2, h2) (l1, h1).
  Proof.
    move=> Hl2 Hl1 Hh1 Hnb2.
    destruct l1 as [|l1'], h1 as [|h1'], h2 as [|h2'];
      unfold interval_quot_pos_across_opt, interval_quot_pos_across,
        interval_quot_pos_neg, interval_quot_pos, interval_opp,
        neg_bound, quot_bound, join_itv;
      unfold Conjunction.join; simpl;
      unfold min_opt, max_opt; simpl;
      simpl in Hl1; unfold_set in Hl1;
      simpl in Hh1; unfold_set in Hh1;
      simpl in Hnb2;
      rewrite ?Z.quot_1_r.
    all: try reflexivity.
    all: repeat f_equal.
    all: try lia.
    (* The remaining goals are just two shapes — a [Z.min] lower bound
       and a [Z.max] upper bound — each occurring twice; one [first]
       dispatches both. *)
    all: first
      [ rewrite Z.min_l => //; transitivity 0;
          [ lia | apply Z.quot_pos; lia ]
      | rewrite Z.max_r => //; transitivity 0;
          [ apply Z.opp_le_mono; rewrite Z.opp_involutive;
            replace (-0) with 0 by lia; apply Z.quot_pos; lia
          | lia ] ].
  Qed.

  Lemma interval_quot_pos_across_opt_best (l2 : Z) (h2 : WithTop.with_top Z)
    (l1 h1 : WithTop.with_top Z) :
    0 <= l2 ->
    (-1) ∈ γ[glbtop] l1 ->
    1 ∈ γ[lubtop] h1 ->
    non_bottom (WithTop.NotTop l2, h2) ->
    BestAbstraction (A:=itv)
      (interval_quot_pos_across_opt (WithTop.NotTop l2, h2) (l1, h1))
      (collecting_quot
        (γ[itv] (WithTop.NotTop l2, h2))
        (γ[itv] (l1, h1))).
  Proof.
    move=> Hl2 Hl1 Hh1 Hnb2.
    rewrite interval_quot_pos_across_eq //.
    exact: interval_quot_pos_across_best.
  Qed.

  Lemma interval_quot_neg_across_opt_best (l2 : WithTop.with_top Z) (h2 : Z)
    (l1 h1 : WithTop.with_top Z) :
    h2 <= 0 ->
    (-1) ∈ γ[glbtop] l1 ->
    1 ∈ γ[lubtop] h1 ->
    non_bottom (l2, WithTop.NotTop h2) ->
    BestAbstraction (A:=itv)
      (interval_quot_neg_across_opt (l2, WithTop.NotTop h2) (l1, h1))
      (collecting_quot
        (γ[itv] (l2, WithTop.NotTop h2))
        (γ[itv] (l1, h1))).
  Proof.
    move=> Hh2 Hl1 Hh1 Hnb2.
    destruct l2 as [|l2'].
    - (* l2 = Top *)
      have Hba := best_abstraction_opp _ _
        (interval_quot_pos_across_opt_best (-h2) WithTop.Top l1 h1
           ltac:(lia) Hl1 Hh1 I).
      apply (best_abstraction_equiv _ _ _ Hba).
      unfold_set_equiv; simpl; move=> z;
      split; move=> [c2 [c1 [Hc2 [[Hc1 Hc1'] [Hne Hz]]]]];
        exists (-c2), c1; repeat split;
        (try done; try (unfold_set in *; simpl in *; lia);
         try (rewrite Z.quot_opp_l; lia)).
    - (* l2 = NotTop l2' *)
      have Hnb2' : non_bottom (WithTop.NotTop (-h2), WithTop.NotTop (-l2'))
        by simpl; simpl in Hnb2; lia.
      have Hba := best_abstraction_opp _ _
        (interval_quot_pos_across_opt_best (-h2) (WithTop.NotTop (-l2')) l1 h1
           ltac:(lia) Hl1 Hh1 Hnb2').
      have Heq : interval_opp
        (interval_quot_pos_across_opt (WithTop.NotTop (-h2), WithTop.NotTop (-l2')) (l1, h1))
        = interval_quot_neg_across_opt (WithTop.NotTop l2', WithTop.NotTop h2) (l1, h1).
      { rewrite /interval_opp /interval_quot_pos_across_opt
                /interval_quot_neg_across_opt /neg_bound.
        congr pair; apply f_equal; apply Z.opp_involutive. }
      rewrite Heq in Hba.
      apply (best_abstraction_equiv _ _ _ Hba).
      unfold_set_equiv; simpl; move=> z;
      split; move=> [c2 [c1 [Hc2 [[Hc1 Hc1'] [Hne Hz]]]]];
        exists (-c2), c1; repeat split;
        (try done; try (unfold_set in *; simpl in *; lia);
         try (rewrite Z.quot_opp_l; lia)).
  Qed.


  (** Best abstraction for neg/across case: dividend ≤ 0, divisor crosses 0.
      Mirror of [interval_quot_pos_across_best]. *)
  Lemma interval_quot_neg_across_best (l2 : WithTop.with_top Z) (h2 : Z)
    (l1 h1 : WithTop.with_top Z) :
    h2 <= 0 ->
    (-1) ∈ γ[glbtop] l1 ->
    1 ∈ γ[lubtop] h1 ->
    non_bottom (l2, WithTop.NotTop h2) ->
    BestAbstraction (A:=itv)
      (interval_quot_neg_across (l2, WithTop.NotTop h2) (l1, h1))
      (collecting_quot
        (γ[itv] (l2, WithTop.NotTop h2))
        (γ[itv] (l1, h1))).
  Proof.
    move=> Hh2 Hl1 Hh1 Hnb2.
    have Hnb1n: non_bottom (l1, WithTop.NotTop (-1))
      by case: l1 Hl1 => [|?] //; unfold_set; simpl; lia.
    have Hnb1p: non_bottom (WithTop.NotTop 1, h1)
      by case: h1 Hh1 => [|?] //; unfold_set; simpl; lia.
    have Hl1' : 0 ∈ γ[glbtop] l1.
    { destruct l1; [done | unfold_set in Hl1; unfold_set; simpl in *; lia]. }
    have Hh1' : 0 ∈ γ[lubtop] h1.
    { destruct h1; [done | unfold_set in Hh1; unfold_set; simpl in *; lia]. }
    have /is_alpha_iff_best_abstraction Hn :=
      interval_quot_neg_neg_best l2 h2 l1 (-1)
        Hh2 ltac:(lia) Hnb2 Hnb1n.
    have /is_alpha_iff_best_abstraction Hp :=
      interval_quot_neg_pos_best l2 h2 1 h1
        Hh2 ltac:(lia) Hnb2 Hnb1p.
    apply/is_alpha_iff_best_abstraction.
    apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp).
    apply/propset_equiv_iff => z; exact: (collecting_quot_split_divisor _ _ _ z Hl1' Hh1').
  Qed.

  (** Best abstraction for across/across case: both dividend and divisor cross 0.
      Splits dividend at 0 and uses pos_across_opt + neg_across_opt. *)
  Lemma interval_quot_across_across_best (l2 : Z) (h2 : WithTop.with_top Z)
    (l1 h1 : WithTop.with_top Z) :
    l2 <= 0 ->
    0 ∈ γ[lubtop] h2 ->
    (-1) ∈ γ[glbtop] l1 ->
    1 ∈ γ[lubtop] h1 ->
    non_bottom (WithTop.NotTop l2, h2) ->
    BestAbstraction (A:=itv)
      (interval_quot_across_across (WithTop.NotTop l2, h2) (l1, h1))
      (collecting_quot
        (γ[itv] (WithTop.NotTop l2, h2))
        (γ[itv] (l1, h1))).
  Proof.
    move=> Hl2 Hh2 Hl1 Hh1 Hnb2.
    have Hnb2n: non_bottom (WithTop.NotTop l2, WithTop.NotTop 0) by simpl; lia.
    have Hnb2p: non_bottom (WithTop.NotTop 0, h2)
      by case: h2 Hh2 Hnb2 => [|?] //; unfold_set; simpl; lia.
    have Hl2' : 0 ∈ γ[glbtop] (WithTop.NotTop l2) by unfold_set; simpl; lia.
    have /is_alpha_iff_best_abstraction Hn :=
      interval_quot_neg_across_opt_best (WithTop.NotTop l2) 0 l1 h1
        (Z.le_refl 0) Hl1 Hh1 Hnb2n.
    have /is_alpha_iff_best_abstraction Hp :=
      interval_quot_pos_across_opt_best 0 h2 l1 h1
        (Z.le_refl 0) Hl1 Hh1 Hnb2p.
    apply/is_alpha_iff_best_abstraction.
    apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp).
    apply/propset_equiv_iff => z; exact: (collecting_quot_split_dividend _ _ _ z Hl2' Hh2).
  Qed.

  (** Generalization of [interval_quot_across_across_best] to allow [l2] unbounded.
      The constraint [l2 <= 0] is replaced by the more uniform [0 ∈ γ[glbtop] l2]. *)
  Lemma interval_quot_across_across_best_gen (l2 h2 : WithTop.with_top Z)
    (l1 h1 : WithTop.with_top Z) :
    0 ∈ γ[glbtop] l2 ->
    0 ∈ γ[lubtop] h2 ->
    (-1) ∈ γ[glbtop] l1 ->
    1 ∈ γ[lubtop] h1 ->
    non_bottom (l2, h2) ->
    BestAbstraction (A:=itv)
      (interval_quot_across_across (l2, h2) (l1, h1))
      (collecting_quot
        (γ[itv] (l2, h2))
        (γ[itv] (l1, h1))).
  Proof.
    move=> Hl2 Hh2 Hl1 Hh1 Hnb2.
    have Hnb2n: non_bottom (l2, WithTop.NotTop 0).
    { case: l2 Hl2 Hnb2 => [|?] //=; unfold_set; simpl; lia. }
    have Hnb2p: non_bottom (WithTop.NotTop 0, h2).
    { case: h2 Hh2 Hnb2 => [|?] //=; unfold_set; simpl; lia. }
    have /is_alpha_iff_best_abstraction Hn :=
      interval_quot_neg_across_opt_best l2 0 l1 h1
        (Z.le_refl 0) Hl1 Hh1 Hnb2n.
    have /is_alpha_iff_best_abstraction Hp :=
      interval_quot_pos_across_opt_best 0 h2 l1 h1
        (Z.le_refl 0) Hl1 Hh1 Hnb2p.
    apply/is_alpha_iff_best_abstraction.
    apply: (is_alpha_join_split _ _ _ _ _ _ _ Hn Hp).
    apply/propset_equiv_iff => z; exact: (collecting_quot_split_dividend _ _ _ z Hl2 Hh2).
  Qed.

  Lemma interval_quot_full_best i1 i2:
    non_bottom i1 -> non_bottom i2 ->
    classify_divisor i1 <> DivZero ->
    BestAbstraction (A:=itv) (interval_quot_full i2 i1)
      (collecting_quot (γ[itv] i2) (γ[itv] i1)).
  Proof.
    move: i1 i2 => [l1 h1] [l2 h2] Hnb1 Hnb2 HnZ.
    rewrite /interval_quot_full.
    destruct (classify_divisor (l1, h1)) as [iP | iN | | ] eqn:Hcd.
    - (* DivPos iP *)
      clear HnZ.
      move: iP Hcd => [l1s h1s] Hcd.
      move: (classify_divisor_pos_inv_alt _ _ _ _ Hnb1 Hcd) =>
        [Hh [[ll [ll' [Heq2 [Heq3 Hlia]]]] [Hnb1' Heqconc]]].
      move: Hh Heq2 Heq3 Hcd Heqconc Hnb1' => -> -> -> Hcd Heqconc Hnb1'.
      apply best_abstraction_equiv with
        (S := collecting_quot (γ[itv] (l2,h2)) (γ[itv] (WithTop.NotTop ll', h1))).
      2: { exact: collecting_quot_restrict_equiv Heqconc. }
      case Hc2: (classify (l2, h2)) => [| |].
      + (* Pos, Pos case. *)
        have [l2' [Hl2eq Hl2']] := classify_Pos_inv _ _ Hc2.
        rewrite Hl2eq in Hnb2 *.
        apply interval_quot_pos_best => //. lia.
      + (* Pos, Neg case. *)
        have [h2' [Hh2eq Hh2']] := classify_Neg_inv _ _ Hc2.
        rewrite Hh2eq in Hnb2 *.
        apply: (interval_quot_neg_pos_best _ _ _ _ Hh2' _ Hnb2 Hnb1'); lia.
      + (* Pos, Across case. *)
        have [Hl2g Hh2l] := classify_Across_inv _ _ Hnb2 Hc2.
        apply: (interval_quot_across_pos_best _ _ _ _ Hl2g Hh2l _ Hnb2 Hnb1'); lia.
    - (* DivNeg iN *)
      clear HnZ.
      move: iN Hcd => [l1s h1s] Hcd.
      move: (classify_divisor_neg_inv_alt _ _ _ _ Hnb1 Hcd) =>
        [Hl [[hh [hh' [Heq2 [Heq3 Hlia]]]] [Hnb1' Heqconc]]].
      move: Hl Heq2 Heq3 Hcd Heqconc Hnb1' => -> -> -> Hcd Heqconc Hnb1'.
      apply best_abstraction_equiv with
        (S := collecting_quot (γ[itv] (l2,h2)) (γ[itv] (l1, WithTop.NotTop hh'))).
      2: { exact: collecting_quot_restrict_equiv Heqconc. }
      case Hc2: (classify (l2, h2)) => [| |].
      + (* Neg, Pos case. *)
        have [l2' [Hl2eq Hl2']] := classify_Pos_inv _ _ Hc2.
        rewrite Hl2eq in Hnb2 *.
        apply: (interval_quot_pos_neg_best _ _ _ _ Hl2' _ Hnb2 Hnb1'); lia.
      + (* Neg, Neg case. *)
        have [h2' [Hh2eq Hh2']] := classify_Neg_inv _ _ Hc2.
        rewrite Hh2eq in Hnb2 *.
        apply: (interval_quot_neg_neg_best _ _ _ _ Hh2' _ Hnb2 Hnb1'); lia.
      + (* Neg, Across case. *)
        have [Hl2g Hh2l] := classify_Across_inv _ _ Hnb2 Hc2.
        apply: (interval_quot_across_neg_best _ _ _ _ Hl2g Hh2l _ Hnb2 Hnb1'); lia.
    - (* DivZero: excluded by hypothesis *)
      by case: HnZ.
    - (* DivAcross *)
      have [Hm1 Hp1] := classify_divisor_across_inv _ _ Hcd.
      have Hmm1 : (-1) ∈ γ[glbtop] l1.
      { unfold_set in Hm1; by move: Hm1 => [? _]. }
      have Hpp1 : 1 ∈ γ[lubtop] h1.
      { unfold_set in Hp1; by move: Hp1 => [_ ?]. }
      case Hc2: (classify (l2, h2)) => [| |].
      + (* across/Pos *)
        have [l2' [Hl2eq Hl2']] := classify_Pos_inv _ _ Hc2.
        rewrite Hl2eq in Hnb2 *.
        apply: (interval_quot_pos_across_best _ _ _ _ Hl2' Hmm1 Hpp1 Hnb2).
      + (* across/Neg *)
        have [h2' [Hh2eq Hh2']] := classify_Neg_inv _ _ Hc2.
        rewrite Hh2eq in Hnb2 *.
        apply: (interval_quot_neg_across_best _ _ _ _ Hh2' Hmm1 Hpp1 Hnb2).
      + (* across/Across *)
        have [Hl2g Hh2l] := classify_Across_inv _ _ Hnb2 Hc2.
        exact: (interval_quot_across_across_best_gen _ _ _ _ Hl2g Hh2l Hmm1 Hpp1 Hnb2).
  Qed.



End Interval_quot.
