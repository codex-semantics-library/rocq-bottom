(* MulTheory.v - [Z.mul] transfer function for the ZInterval single-value
   abstraction: [interval_mul] on two intervals. Split out of Z_interval.v. *)

(* STATUS: mul (Z.mul): sound + best (α-complete)
     (interval_mul_opt_best, interval_mul_opt_alpha_complete).
   Uses the negation transfer function ([neg_bound], [interval_opp]), now in
   [OpsComp.v], and the split-at-zero α-machinery, still in Z_interval.v.

   The extracted [bound_mul] and [interval_mul_opt] live in [OpsComp.v]; the
   proof-only mirror [interval_mul_math] stays here. *)

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
Require Import Transfer_function.ZInterval.OpsComp.
Require Import Transfer_function.ZInterval.OppTheory.
Open Scope Z_scope.
Generalizable All Variables.

(** * Unboundedness and zero-collapse of [Z.mul] product sets.

    Stated over [collecting_binary_forward Z.mul], so they belong with the
    multiplication transfer function rather than with the interval
    abstraction; [interval_mul_opt_best] below is their only client. *)

(** When one operand of [Z.mul] ranges over an [IsAlpha Top] (unbounded) set
    and the other contains a strictly positive element, the product set is
    itself unbounded above. Right-unbounded variant: the unbounded factor is
    the right argument. *)
Lemma IsAlpha_lubtop_top_product_r (S_pos S_unb : ℘ Z) :
  IsAlpha (A:=lubtop) WithTop.Top S_unb ->
  (exists c, c ∈ S_pos /\ 0 < c) ->
  IsAlpha (A:=lubtop) WithTop.Top
    (collecting_binary_forward Z.mul S_pos S_unb).
Proof.
  move=> Hunb [c2 [Hc2in Hc2pos]].
  rewrite /IsAlpha => a; case: a => [|z] /=.
  - by unfold_set; split.
  - unfold_set; split; [|by []].
    move=> Hsub.
    apply: (is_alpha_lubtop_top_nn S_unb (Z.max z 0) Hunb) => [[c1 [Hc1in Hc1gt]]].
    have Hle := Hsub (c2 * c1) ltac:(exists c2, c1; by repeat split).
    unfold_set in Hle. nia.
Qed.

(** Left-unbounded variant. *)
Lemma IsAlpha_lubtop_top_product_l (S_unb S_pos : ℘ Z) :
  IsAlpha (A:=lubtop) WithTop.Top S_unb ->
  (exists c, c ∈ S_pos /\ 0 < c) ->
  IsAlpha (A:=lubtop) WithTop.Top
    (collecting_binary_forward Z.mul S_unb S_pos).
Proof.
  move=> Hunb [c1 [Hc1in Hc1pos]].
  rewrite /IsAlpha => a; case: a => [|z] /=.
  - by unfold_set; split.
  - unfold_set; split; [|by []].
    move=> Hsub.
    apply: (is_alpha_lubtop_top_nn S_unb (Z.max z 0) Hunb) => [[c2 [Hc2in Hc2gt]]].
    have Hle := Hsub (c2 * c1) ltac:(exists c2, c1; by repeat split).
    unfold_set in Hle. nia.
Qed.

(** When one operand of [Z.mul] is collapsed to the singleton [{0}], every
    product is [0], so the LUB of the product set is [NotTop 0]. Left-zero
    variant. *)
Lemma zero_interval_product_lub_l (S_zero S_other : ℘ Z) :
  (forall c, c ∈ S_zero -> c = 0) ->
  (exists c, c ∈ S_zero) ->
  (exists c, c ∈ S_other) ->
  IsAlpha (A:=lubtop) (WithTop.NotTop 0)
    (collecting_binary_forward Z.mul S_zero S_other).
Proof.
  move=> Hzero [c0 Hc0] [c1 Hc1].
  have H0z : 0 ∈ S_zero by have E := Hzero c0 Hc0; rewrite -E.
  apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_lubtop)).
  constructor.
  - move=> z' [c2 [c1' [Hc2in [Hc1'in <-]]]].
    have -> : c2 = 0 by apply Hzero.
    unfold_set; simpl; lia.
  - move=> z' Hz'; apply Hz'.
    exists 0, c1; split; [exact H0z | split; [exact Hc1 | ring]].
Qed.

(** Right-zero variant. *)
Lemma zero_interval_product_lub_r (S_other S_zero : ℘ Z) :
  (forall c, c ∈ S_zero -> c = 0) ->
  (exists c, c ∈ S_zero) ->
  (exists c, c ∈ S_other) ->
  IsAlpha (A:=lubtop) (WithTop.NotTop 0)
    (collecting_binary_forward Z.mul S_other S_zero).
Proof.
  move=> Hzero [c0 Hc0] [c1 Hc1].
  have H0z : 0 ∈ S_zero by have E := Hzero c0 Hc0; rewrite -E.
  apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_lubtop)).
  constructor.
  - move=> z' [c2 [c1' [Hc2in [Hc1'in <-]]]].
    have -> : c1' = 0 by apply Hzero.
    unfold_set; simpl; lia.
  - move=> z' Hz'; apply Hz'.
    exists c1, 0; split; [exact Hc1 | split; [exact H0z | ring]].
Qed.

Section Interval_mul.

  (** * Extended integers with signed infinity (used by _best lemmas). *)

  (** Extended integers: Z augmented with -∞ and +∞. *)
  Inductive with_infinity :=
  | NInf                        (* -∞ *)
  | Fin : Z -> with_infinity    (* finite *)
  | PInf.                       (* +∞ *)

  Definition high_inf (h : WithTop.with_top Z) : with_infinity :=
    match h with WithTop.Top => PInf | WithTop.NotTop z => Fin z end.

  Definition to_high (x : with_infinity) : WithTop.with_top Z :=
    match x with PInf => WithTop.Top | Fin z => WithTop.NotTop z | NInf => WithTop.NotTop 0 (* dummy *) end.

  (** Multiplication on extended integers.
      Convention: 0 × ±∞ = 0 (standard in interval arithmetic). *)
  Definition mul_inf (a b : with_infinity) : with_infinity :=
    match a, b with
    | Fin 0, _ | _, Fin 0 => Fin 0
    | Fin x, Fin y => Fin (x * y)
    | NInf, Fin y | Fin y, NInf =>
        if y >? 0 then NInf else PInf
    | PInf, Fin y | Fin y, PInf =>
        if y >? 0 then PInf else NInf
    | NInf, NInf | PInf, PInf => PInf
    | NInf, PInf | PInf, NInf => NInf
    end.

  Lemma mul_inf_fin (x y : Z) : mul_inf (Fin x) (Fin y) = Fin (x * y).
  Proof. by case: x => [|?|?]; case: y => [|?|?] => //=; lia. Qed.

  (** * Best abstraction: positive × positive case, split into lower/upper bounds. *)

  (** Abstract transfer function for positive × positive interval
      multiplication.  The result's lower bound is the product of the
      lower bounds; the upper bound is [mul_inf] of the high bounds,
      projected back via [to_high]. *)
  Definition interval_mul_pos (i2 i1 : interval) : interval :=
    let '(l2, h2) := i2 in let '(l1, h1) := i1 in
    (WithTop.lift2 Z.mul l1 l2,
     to_high (mul_inf (high_inf h1) (high_inf h2))).

  (** * Best abstraction: negative × negative case. *)

  Lemma glbtop_neg_lubtop (l : WithTop.with_top Z) c :
    c ∈ γ[glbtop] l -> (-c) ∈ γ[lubtop] (neg_bound l).
  Proof. by case: l; unfold_set => /=; lia. Qed.

  Lemma lubtop_neg_glbtop (l : WithTop.with_top Z) c :
    c ∈ γ[lubtop] (neg_bound l) -> (-c) ∈ γ[glbtop] l.
  Proof. by case: l; unfold_set => /=; lia. Qed.

  (** * Best abstraction: positive × positive, full.
      Combines GLB (pos_glb) and LUB (pos_upper) via the
      [Conjunction.best_abstraction_pair_iff] gluing lemma. *)
  Lemma interval_mul_pos_alpha_complete
        (l1 l2 : Z) (h1 h2 : WithTop.with_top Z) (S2 S1 : ℘ Z) :
    0 <= l1 -> 0 <= l2 ->
    non_bottom (WithTop.NotTop l1, h1) ->
    non_bottom (WithTop.NotTop l2, h2) ->
    (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
    binary_alpha_complete itv itv itv interval_mul_pos
      (collecting_binary_forward Z.mul)
      (WithTop.NotTop l2, h2) (WithTop.NotTop l1, h1) S2 S1.
  Proof.
    rewrite /binary_alpha_complete => Hl1 Hl2 Hnb1 Hnb2 Hex2 Hex1 Ha2 Ha1.
    have HS2 := gamma_alpha_extensive itv _ _ Ha2.
    have HS1 := gamma_alpha_extensive itv _ _ Ha1.
    apply: (itv_attained_low_witness (WithTop.NotTop l2) h2 S2 Ha2 Hex2) => /= Hatl2.
    apply: (itv_attained_low_witness (WithTop.NotTop l1) h1 S1 Ha1 Hex1) => /= Hatl1.
    apply: (itv_attained_high_witness (WithTop.NotTop l2) h2 S2 Ha2 Hex2) => Hath2.
    apply: (itv_attained_high_witness (WithTop.NotTop l1) h1 S1 Ha1 Hex1) => Hath1.
    move: (Ha2) => /Conjunction.is_alpha_pair_iff [_ Hlub2].
    move: (Ha1) => /Conjunction.is_alpha_pair_iff [_ Hlub1].
    apply/Conjunction.is_alpha_pair_iff; split.
    - (* GLB: l1*l2 is the glb of the product set *)
      apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_glbtop)).
      constructor.
      + move=> z [c2 [c1 [Hc2 [Hc1 <-]]]].
        have Hg1 := HS1 _ Hc1. have Hg2 := HS2 _ Hc2.
        clear HS1 HS2 Hlub1 Hlub2 Ha1 Ha2 Hath1 Hath2 Hatl1 Hatl2.
        move: Hg1 Hg2 Hnb1 Hnb2.
        case: h1 => [|?]; case: h2 => [|?];
          unfold_set; simpl => *; nia.
      + move=> z Hz; apply Hz.
        exists l2, l1; by repeat split; [exact Hatl2|exact Hatl1|ring].
    - (* LUB: mul_inf of the high bounds *)
      move: Hnb1 Hnb2 Hath1 Hath2 Hlub1 Hlub2 Ha1 Ha2 HS1 HS2;
      case: h1 => [|h1']; case: h2 => [|h2'] /=
        => Hnb1 Hnb2 Hath1 Hath2 Hlub1 Hlub2 Ha1 Ha2 HS1 HS2.
      + (* Top, Top → unbounded, result Top *)
        apply: (is_alpha_lubtop_top_witness S2 0 Hlub2) => Hpos2.
        exact: (IsAlpha_lubtop_top_product_r _ _ Hlub1 Hpos2).
      + (* Top, NotTop h2' *)
        move: Hnb2 Hlub2 Ha2 HS2 Hath2;
        case: h2' => [|h2'|h2'] /= Hnb2 Hlub2 Ha2 HS2 Hath2.
        * (* h2' = 0 → S2 ⊆ {0}, products are all 0 *)
          apply: zero_interval_product_lub_l; [|exact Hex2|exact Hex1].
          move=> c Hc. have Hg := HS2 _ Hc; unfold_set in Hg.
          destruct Hg as [Hgl Hgh]. lia.
        * (* h2' > 0 → unbounded *)
          apply: (IsAlpha_lubtop_top_product_r _ _ Hlub1).
          exists (Z.pos h2'); split; [exact Hath2 | lia].
        * exfalso; lia.
      + (* NotTop h1', Top → symmetric *)
        move: Hnb1 Hlub1 Ha1 HS1 Hath1;
        case: h1' => [|h1'|h1'] /= Hnb1 Hlub1 Ha1 HS1 Hath1.
        * (* h1' = 0 → S1 ⊆ {0}, products are all 0 *)
          apply: zero_interval_product_lub_r; [|exact Hex1|exact Hex2].
          move=> c Hc. have Hg := HS1 _ Hc; unfold_set in Hg.
          destruct Hg as [Hgl Hgh]. lia.
        * (* h1' > 0 → unbounded *)
          apply: (IsAlpha_lubtop_top_product_l _ _ Hlub2).
          exists (Z.pos h1'); split; [exact Hath1 | lia].
        * exfalso; lia.
      + (* NotTop h1', NotTop h2' — both finite *)
        have -> : to_high (mul_inf (high_inf (WithTop.NotTop h1')) (high_inf (WithTop.NotTop h2')))
                  = WithTop.NotTop (h1' * h2') by rewrite /high_inf mul_inf_fin.
        apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_lubtop)).
        rewrite /LUBUnbounded.is_α /=. constructor.
        * move=> z' [c2 [c1 [Hc2 [Hc1 <-]]]].
          have Hg1 := HS1 _ Hc1; have Hg2 := HS2 _ Hc2.
          unfold_set in Hg1; unfold_set in Hg2.
          destruct Hg1 as [? ?]; destruct Hg2 as [? ?]; nia.
        * move=> z' Hz'; apply Hz'.
          exists h2', h1'; by repeat split; [exact Hath2|exact Hath1|ring].
  Qed.

  (** Non-emptiness transfers through negation. *)
  Local Lemma opp_nonempty (S : ℘ Z) : (exists c, c ∈ S) -> exists c, c ∈ {[ z | -z ∈ S ]}.
  Proof.
    move=> [c Hc]. exists (-c). by unfold_set; replace (- - c) with c by lia.
  Qed.

  (** Reindexing an existential through negation on [Z]: lets us align
      witnesses on both sides of a mul/opp commutation. Mirrors the TODO
      at [base.v:358]. *)
  Local Lemma exists_iff_opp {P Q : Z -> Prop} :
    (forall x, P x <-> Q (-x)) ->
    (exists x, P x) <-> (exists x, Q x).
  Proof.
    move=> H; split=> [[x /H Hx] | [x Hx]].
    - by exists (-x).
    - exists (-x); apply H. by replace (- - x) with x by lia.
  Qed.

  (** [Z.mul] commutes with negation on either argument: side conditions
      for [binary_alpha_complete_opp_l] / [_opp_r]. *)
  Lemma collecting_mul_opp_l (T2 T1 : ℘ Z) :
    collecting_binary_forward Z.mul {[ z | -z ∈ T2 ]} T1 ⊆⊇
    {[ z | -z ∈ collecting_binary_forward Z.mul T2 T1 ]}.
  Proof.
    unfold_set_equiv => c.
    apply: exists_iff_opp => c2; apply: exists_iff => c1; unfold_set.
    by split; move=> [? [? ?]]; repeat split=> //; lia.
  Qed.

  Lemma collecting_mul_opp_r (T2 T1 : ℘ Z) :
    collecting_binary_forward Z.mul T2 {[ z | -z ∈ T1 ]} ⊆⊇
    {[ z | -z ∈ collecting_binary_forward Z.mul T2 T1 ]}.
  Proof.
    unfold_set_equiv => c.
    apply: exists_iff => c2; apply: exists_iff_opp => c1; unfold_set.
    by split; move=> [? [? ?]]; repeat split=> //; lia.
  Qed.

  (** α-completeness for negative × positive case, derived from the
      positive instance via right-argument opp transport. *)
  Lemma interval_mul_neg_pos_alpha_complete
      (l2 : Z) (h2 : WithTop.with_top Z)
      (l1 : WithTop.with_top Z) (h1 : Z) (S2 S1 : ℘ Z) :
    0 <= l2 -> h1 <= 0 ->
    non_bottom (WithTop.NotTop l2, h2) ->
    non_bottom (l1, WithTop.NotTop h1) ->
    (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
    binary_alpha_complete itv itv itv
      (fun b2 b1 => interval_opp (interval_mul_pos b2 (interval_opp b1)))
      (collecting_binary_forward Z.mul)
      (WithTop.NotTop l2, h2) (l1, WithTop.NotTop h1) S2 S1.
  Proof.
    move=> Hl2 Hh1 Hnb2 Hnb1 Hex2 Hex1.
    rewrite /binary_alpha_complete => Ha2 Ha1.
    apply (is_alpha_opp_iff _ _).1 in Ha1.
    have Hnb1': non_bottom (WithTop.NotTop (-h1), neg_bound l1)
      by case: l1 Hnb1 Ha1 => [_ | x Hx] _ /=; [done | move: Hx => /= Hx; lia].
    have Hex1' := opp_nonempty _ Hex1.
    have Hpos := interval_mul_pos_alpha_complete (-h1) l2 (neg_bound l1) h2
                   S2 {[ z | -z ∈ S1 ]}
                   ltac:(lia) Hl2 Hnb1' Hnb2 Hex2 Hex1' Ha2 Ha1.
    apply (is_alpha_opp_iff _ _).1 in Hpos.
    apply: (is_alpha_set_equiv _ _ _ _ Hpos).
    split=> z.
    - unfold_set => -[c2 [c1 [Hc2 [Hc1 Heq]]]]; unfold_set in Hc1.
      exists c2, (-c1); repeat split; [exact Hc2 | exact Hc1 | lia].
    - move=> [c2 [c1 [Hc2 [Hc1 <-]]]]; unfold_set.
      exists c2, (-c1); unfold_set; repeat split.
      + exact Hc2.
      + by replace (- - c1) with c1 by lia.
      + lia.
  Qed.

  (** α-completeness for negative × negative case, derived via both opp transports. *)
  Lemma interval_mul_neg_neg_alpha_complete
      (l2 l1 : WithTop.with_top Z) (h2 h1 : Z) (S2 S1 : ℘ Z) :
    h2 <= 0 -> h1 <= 0 ->
    non_bottom (l2, WithTop.NotTop h2) ->
    non_bottom (l1, WithTop.NotTop h1) ->
    (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
    binary_alpha_complete itv itv itv
      (fun b2 b1 => interval_mul_pos (interval_opp b2) (interval_opp b1))
      (collecting_binary_forward Z.mul)
      (l2, WithTop.NotTop h2) (l1, WithTop.NotTop h1) S2 S1.
  Proof.
    move=> Hh2 Hh1 Hnb2 Hnb1 Hex2 Hex1.
    rewrite /binary_alpha_complete => Ha2 Ha1.
    apply (is_alpha_opp_iff _ _).1 in Ha1.
    apply (is_alpha_opp_iff _ _).1 in Ha2.
    have Hnb1': non_bottom (WithTop.NotTop (-h1), neg_bound l1)
      by case: l1 Hnb1 Ha1 => [_ | x Hx] _ /=; [done | move: Hx => /= Hx; lia].
    have Hnb2': non_bottom (WithTop.NotTop (-h2), neg_bound l2)
      by case: l2 Hnb2 Ha2 => [_ | x Hx] _ /=; [done | move: Hx => /= Hx; lia].
    have Hex1' := opp_nonempty _ Hex1.
    have Hex2' := opp_nonempty _ Hex2.
    have Hpos := interval_mul_pos_alpha_complete (-h1) (-h2)
                   (neg_bound l1) (neg_bound l2)
                   {[ z | -z ∈ S2 ]} {[ z | -z ∈ S1 ]}
                   ltac:(lia) ltac:(lia) Hnb1' Hnb2' Hex2' Hex1' Ha2 Ha1.
    apply: (is_alpha_set_equiv _ _ _ _ Hpos).
    (* collecting_binary_forward Z.mul {[z|-z∈S2]} {[z|-z∈S1]} ⊆⊇
       collecting_binary_forward Z.mul S2 S1 *)
    split=> z; unfold_set.
    - move=> [c2 [c1 [Hc2 [Hc1 <-]]]]; unfold_set in Hc1; unfold_set in Hc2.
      exists (-c2), (-c1); unfold_set; repeat split.
      + by replace (- - c2) with c2 by lia.
      + by replace (- - c1) with c1 by lia.
      + ring.
    - move=> [c2 [c1 [Hc2 [Hc1 <-]]]].
      exists (-c2), (-c1); unfold_set; repeat split.
      + by replace (- - c2) with c2 by lia.
      + by replace (- - c1) with c1 by lia.
      + ring.
  Qed.

  (** * Best abstraction: positive × negative case (by commutativity). *)

  Lemma collecting_mul_comm (S1 S2: propset Z) z :
    z ∈ collecting_binary_forward Z.mul S1 S2 <->
    z ∈ collecting_binary_forward Z.mul S2 S1.
  Proof.
    by unfold_set; split; move=> [a [b [Ha [Hb Hab]]]];
      exists b, a; repeat split; try assumption; lia.
  Qed.


  (** * Infrastructure for across-zero cases. *)

  (** γ of an across-zero interval splits at 0 into the negative-half γ and
      positive-half γ. Operand-level statement; product-level splits follow
      via [collecting_binary_forward_union_l] (Abstraction.v). *)
  Lemma gamma_itv_split_at_zero_l (l h : WithTop.with_top Z) :
    0 ∈ γ[glbtop] l -> 0 ∈ γ[lubtop] h ->
    γ[itv] (l, h) ⊆⊇ γ[itv] (l, WithTop.NotTop 0) ∪ γ[itv] (WithTop.NotTop 0, h).
  Proof.
    move=> Hl Hh; split=> z.
    - unfold_set => -[Hzl Hzh]; unfold_set.
      case: (Z.le_ge_cases z 0) => Hz; [left | right]; unfold_set; split=> //=; lia.
    - unfold_set => -[Hz | Hz]; unfold_set in Hz; move: Hz => [Hzl Hzh];
        unfold_set; split=> //.
      + by case: h Hh Hzh => [|?]; unfold_set; simpl in *; lia.
      + by case: l Hl Hzl => [|?]; unfold_set; simpl in *; lia.
  Qed.

  (** If an interval contains 0 (across-zero), its product set splits into
      a negative-part product and a positive-part product. Proved directly
      by case-splitting the left operand on its sign; this is the
      element-wise analogue of [gamma_itv_split_at_zero_l] composed with
      [collecting_binary_forward_union_l], avoiding the missing "collecting
      is proper in its first argument" step that route would require. *)
  Lemma collecting_across_split_left (l2 h2: WithTop.with_top Z) (S: propset Z) z :
    0 ∈ γ[glbtop] l2 ->
    0 ∈ γ[lubtop] h2 ->
    z ∈ collecting_binary_forward Z.mul (γ[itv] (l2, h2)) S <->
    z ∈ (collecting_binary_forward Z.mul (γ[itv] (l2, WithTop.NotTop 0)) S ∪
         collecting_binary_forward Z.mul (γ[itv] (WithTop.NotTop 0, h2)) S).
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

  (** * α-completeness, abstract operands: positive (left) × across (right).

      With both operand sets abstract, split the across (right) operand's
      set into its sign halves [S2n] (best-abstracted by the [Neg]
      interval [(l2neg, NotTop m)]) and [S2p] (by the [Pos] interval
      [(NotTop p, h2)]); the product's best abstraction is the join of
      the two quadrant transfers (pos×neg and pos×pos), by [is_alpha_join].
      The half-abstractions are supplied as hypotheses here (they are
      produced by [itv_split_at_zero_alpha]); the result is left as the
      join — its interior bounds [m]/[p] are exactly the information a
      reduced product could sharpen, so it is deliberately not collapsed
      to the closed [interval_mul] form. *)
  Lemma interval_mul_pos_across_join
    (l1 : Z) (h1 : WithTop.with_top Z)
    (l2neg : WithTop.with_top Z) (m p : Z) (h2 : WithTop.with_top Z)
    (S1 S2n S2p : ℘ Z) :
    0 <= l1 -> m <= 0 -> 0 <= p ->
    non_bottom (WithTop.NotTop l1, h1) ->
    non_bottom (l2neg, WithTop.NotTop m) ->
    non_bottom (WithTop.NotTop p, h2) ->
    (exists c, c ∈ S1) -> (exists c, c ∈ S2n) -> (exists c, c ∈ S2p) ->
    IsAlpha (A:=itv) (WithTop.NotTop l1, h1) S1 ->
    IsAlpha (A:=itv) (l2neg, WithTop.NotTop m) S2n ->
    IsAlpha (A:=itv) (WithTop.NotTop p, h2) S2p ->
    IsAlpha (A:=itv)
      ( join_itv
          (interval_opp (interval_mul_pos (WithTop.NotTop l1, h1)
                           (interval_opp (l2neg, WithTop.NotTop m))))
          (interval_mul_pos (WithTop.NotTop l1, h1) (WithTop.NotTop p, h2)) )
      (collecting_binary_forward Z.mul S1 (S2n ∪ S2p)).
  Proof.
    move=> Hl1 Hm Hp Hnb1 Hnbn Hnbp Hex1 Hexn Hexp Ha1 Han Hap.
    (* Right-operand across-zero split: the [Neg] and [Pos] halves are
       α-complete via *different* quadrant transfers, so the two-function
       [binary_alpha_complete_split_r] is the natural tool; distributivity
       of the product over the [S2n ∪ S2p] split is [_union_r]. *)
    apply: (binary_alpha_complete_split_r _ _ _ _ _ _ _ _ _ _ _ _ _
              (fun T2 => collecting_binary_forward_union_r Z.mul T2 S2n S2p)
              Han Hap
              (interval_mul_neg_pos_alpha_complete l1 h1 l2neg m S1 S2n
                 Hl1 Hm Hnb1 Hnbn Hex1 Hexn)
              (interval_mul_pos_alpha_complete p l1 h2 h1 S1 S2p
                 Hp Hl1 Hnbp Hnb1 Hex1 Hexp)
              Ha1).
  Qed.

  (** Reduction of the bound joins to [Z.min] / [Z.max]. *)
  Lemma min_opt_NotTop (c y : Z) :
    min_opt (WithTop.NotTop c) (WithTop.NotTop y) = WithTop.NotTop (Z.min c y).
  Proof. reflexivity. Qed.
  Lemma max_opt_NotTop (c y : Z) :
    max_opt (WithTop.NotTop c) (WithTop.NotTop y) = WithTop.NotTop (Z.max c y).
  Proof. reflexivity. Qed.
  Lemma min_opt_TopL (y : WithTop.with_top Z) : min_opt WithTop.Top y = WithTop.Top.
  Proof. reflexivity. Qed.
  Lemma min_opt_TopR (x : WithTop.with_top Z) : min_opt x WithTop.Top = WithTop.Top.
  Proof. by case: x. Qed.
  Lemma max_opt_TopL (y : WithTop.with_top Z) : max_opt WithTop.Top y = WithTop.Top.
  Proof. reflexivity. Qed.
  Lemma max_opt_TopR (x : WithTop.with_top Z) : max_opt x WithTop.Top = WithTop.Top.
  Proof. by case: x. Qed.

  (** [to_high ∘ mul_inf ∘ high_inf = bound_mul] on non-negative arguments
      (where no [NInf] dummy arises). *)
  Lemma to_high_mul_inf_nonneg (a b : WithTop.with_top Z) :
    0 ∈ γ[lubtop] a -> 0 ∈ γ[lubtop] b ->
    to_high (mul_inf (high_inf a) (high_inf b)) = bound_mul a b.
  Proof.
    move=> Ha Hb; move: Ha Hb.
    case: a => [|[|a|a]]; case: b => [|[|b|b]]; unfold_set => /=;
      first [ done | move=> *; exfalso; lia ].
  Qed.

  (** [join_itv] is componentwise [min_opt] / [max_opt]. *)
  Lemma join_itv_pair (a b c d : WithTop.with_top Z) :
    join_itv (a, b) (c, d) = (min_opt a c, max_opt b d).
  Proof. reflexivity. Qed.

  (** Sign facts and negation identities for [bound_mul] / [neg_bound]. *)
  Lemma neg_bound_invol (a : WithTop.with_top Z) : neg_bound (neg_bound a) = a.
  Proof. by case: a => [|a] //=; rewrite Z.opp_involutive. Qed.

  Lemma bound_mul_neg_l (a b : WithTop.with_top Z) :
    neg_bound (bound_mul a b) = bound_mul (neg_bound a) b.
  Proof. case: a => [|[|a|a]]; case: b => [|[|b|b]] => //=; f_equal; lia. Qed.

  Lemma neg_bound_glbtop_lubtop (l : WithTop.with_top Z) :
    0 ∈ γ[glbtop] l -> 0 ∈ γ[lubtop] (neg_bound l).
  Proof. case: l => [|x]; first by []. unfold_set => /= Hx; unfold_set => /=; lia. Qed.

  Lemma bound_mul_glbtop (l h : WithTop.with_top Z) :
    0 ∈ γ[glbtop] l -> 0 ∈ γ[lubtop] h -> 0 ∈ γ[glbtop] (bound_mul l h).
  Proof.
    case: l => [|[|l|l]]; case: h => [|[|h|h]]; unfold_set => /=;
      first [ done | move=> *; nia ].
  Qed.

  Lemma bound_mul_lubtop (a b : WithTop.with_top Z) :
    0 ∈ γ[lubtop] a -> 0 ∈ γ[lubtop] b -> 0 ∈ γ[lubtop] (bound_mul a b).
  Proof.
    case: a => [|[|a|a]]; case: b => [|[|b|b]]; unfold_set => /=;
      first [ done | move=> *; nia ].
  Qed.

  (** Absorption: a non-positive lower candidate is dominated by a
      non-negative bound in the [min_opt]; dually for [max_opt]. *)
  Lemma min_opt_absorb_r (X : WithTop.with_top Z) (c : Z) :
    0 <= c -> 0 ∈ γ[glbtop] X -> min_opt X (WithTop.NotTop c) = X.
  Proof.
    move=> Hc; case: X => [|x]; first by rewrite min_opt_TopL.
    unfold_set => /= Hx; rewrite min_opt_NotTop; f_equal; lia.
  Qed.

  Lemma max_opt_absorb_l (c : Z) (Y : WithTop.with_top Z) :
    c <= 0 -> 0 ∈ γ[lubtop] Y -> max_opt (WithTop.NotTop c) Y = Y.
  Proof.
    move=> Hc; case: Y => [|y]; first by rewrite max_opt_TopR.
    unfold_set => /= Hy; rewrite max_opt_NotTop; f_equal; lia.
  Qed.

  (** Absorption equality: the join of the two quadrant transfers (with
      the split's interior bounds [m ≤ 0], [p ≥ 0]) collapses to the
      bound-only closed form [(bound_mul l2 h1, bound_mul h2 h1)]. The
      interior bounds are dominated in the join, so they vanish — this is
      the single step connecting the abstract (split) result to a closed
      form of [interval_mul]. *)
  Lemma interval_mul_pos_across_join_eq
    (l1 m p : Z) (h1 l2 h2 : WithTop.with_top Z) :
    0 <= l1 -> m <= 0 -> 0 <= p ->
    0 ∈ γ[glbtop] l2 -> 0 ∈ γ[lubtop] h2 -> 0 ∈ γ[lubtop] h1 ->
    join_itv
      (interval_opp (interval_mul_pos (WithTop.NotTop l1, h1)
                       (interval_opp (l2, WithTop.NotTop m))))
      (interval_mul_pos (WithTop.NotTop l1, h1) (WithTop.NotTop p, h2))
    = (bound_mul l2 h1, bound_mul h2 h1).
  Proof.
    move=> Hl1 Hm Hp Hl2 Hh2 Hh1.
    case: l2 Hl2 => [|[|l2|l2]] Hl2; case: h2 Hh2 => [|[|h2|h2]] Hh2;
      case: h1 Hh1 => [|[|h1|h1]] Hh1;
      case: l1 Hl1 => [|l1|l1] Hl1; case: m Hm => [|m|m] Hm;
      case: p Hp => [|p|p] Hp;
      rewrite /interval_mul_pos /interval_opp /neg_bound /bound_mul /high_inf
              /to_high /mul_inf /join_itv /Conjunction.join /min_opt /max_opt
              /WithTop.lift2 /=;
      move: Hl1 Hm Hp Hl2 Hh2 Hh1; unfold_set => /= *;
      try (exfalso; lia); try done;
      congr pair; try done; try (congr (WithTop.NotTop); nia).
  Qed.

  (** Fully-abstract α-completeness, positive (left) × across (right):
      both operand sets [S1], [S2] arbitrary. Splits [S2] at zero with
      [itv_split_at_zero_alpha], then applies [interval_mul_pos_across_join].
      The best abstraction (delivered through a [Stable] continuation,
      with the split's interior bounds [m]/[p]) is the join of the two
      quadrant transfers over [collecting Z.mul S1 S2]. *)
  Lemma interval_mul_pos_across_abstract {G : Prop} `{Stable G}
    (l1 : Z) (h1 l2 h2 : WithTop.with_top Z) (S1 S2 : ℘ Z) :
    0 <= l1 -> non_bottom (WithTop.NotTop l1, h1) ->
    0 ∈ γ[glbtop] l2 -> 0 ∈ γ[lubtop] h2 ->
    (exists c, c ∈ S1) -> (exists c, c ∈ S2) ->
    IsAlpha (A:=itv) (WithTop.NotTop l1, h1) S1 ->
    IsAlpha (A:=itv) (l2, h2) S2 ->
    (forall m p, m <= 0 -> 0 <= p ->
       IsAlpha (A:=itv)
         (join_itv
            (interval_opp (interval_mul_pos (WithTop.NotTop l1, h1)
                             (interval_opp (l2, WithTop.NotTop m))))
            (interval_mul_pos (WithTop.NotTop l1, h1) (WithTop.NotTop p, h2)))
         (collecting_binary_forward Z.mul S1 S2) -> G) -> G.
  Proof.
    move=> Hl1 Hnb1 Hl2 Hh2 Hex1 Hex2 Ha1 Ha2 Hk.
    move: (Ha2) => /Conjunction.is_alpha_pair_iff [Hglb2 Hlub2].
    apply: (itv_split_at_zero_alpha l2 h2 S2 Hl2 Hh2 Hex2 Ha2) => m p Hm Hp Han Hap.
    apply: (across_le0_witness l2 S2 Hl2 Hex2 Hglb2) => Hne_neg0.
    apply: (across_ge0_witness h2 S2 Hh2 Hex2 Hlub2) => Hne_pos0.
    have Hexn : exists c, c ∈ {[ z | z ∈ S2 /\ z <= 0 ]}
      by move: Hne_neg0 => [c [Hc Hc0]]; exists c; unfold_set; split.
    have Hexp : exists c, c ∈ {[ z | z ∈ S2 /\ 0 <= z ]}
      by move: Hne_pos0 => [c [Hc Hc0]]; exists c; unfold_set; split.
    have Hnbn : non_bottom (l2, WithTop.NotTop m).
    { apply/non_bottom_non_empty; move: Hexn => [c Hc].
      exists c; exact: (gamma_alpha_extensive itv _ _ Han c Hc). }
    have Hnbp : non_bottom (WithTop.NotTop p, h2).
    { apply/non_bottom_non_empty; move: Hexp => [c Hc].
      exists c; exact: (gamma_alpha_extensive itv _ _ Hap c Hc). }
    have Hjoin := interval_mul_pos_across_join l1 h1 l2 m p h2 S1
                    {[ z | z ∈ S2 /\ z <= 0 ]} {[ z | z ∈ S2 /\ 0 <= z ]}
                    Hl1 Hm Hp Hnb1 Hnbn Hnbp Hex1 Hexn Hexp Ha1 Han Hap.
    apply: (Hk m p Hm Hp).
    apply: (is_alpha_set_equiv _ _ _ _ Hjoin); split=> z; unfold_set.
    - move=> [c1 [c2 [Hc1 [Hc2 Heq]]]].
      exists c1, c2; split; first exact Hc1.
      split; last exact Heq.
      by move: Hc2; unfold_set => -[[? ?]|[? ?]].
    - move=> [c1 [c2 [Hc1 [Hc2 Heq]]]].
      exists c1, c2; split; first exact Hc1.
      split; last exact Heq.
      unfold_set; case: (Z.le_ge_cases c2 0) => Hsgn; [left|right]; split=> //.
  Qed.

  (** A non-bottom positive-low interval has a non-negative high bound. *)
  Lemma itv_gamma_lubtop_nonneg (l1 c : Z) (h1 : WithTop.with_top Z) :
    0 <= l1 -> c ∈ γ[itv] (WithTop.NotTop l1, h1) -> 0 ∈ γ[lubtop] h1.
  Proof. move=> Hl1; case: h1 => [|x]; unfold_set => /= *; lia. Qed.

  (** Closed-form α-completeness, positive (left) × across (right), both
      operand sets abstract: the best abstraction of [collecting Z.mul S1 S2]
      is exactly [(bound_mul l2 h1, bound_mul h2 h1)] — the bound-only
      form (= [interval_mul_opt]'s [Across, Pos] branch). Obtained from
      [interval_mul_pos_across_abstract] by collapsing the join via
      [interval_mul_pos_across_join_eq]. *)
  Lemma interval_mul_pos_across_closed
    (l1 : Z) (h1 l2 h2 : WithTop.with_top Z) (S1 S2 : ℘ Z) :
    0 <= l1 -> non_bottom (WithTop.NotTop l1, h1) ->
    0 ∈ γ[glbtop] l2 -> 0 ∈ γ[lubtop] h2 ->
    (exists c, c ∈ S1) -> (exists c, c ∈ S2) ->
    IsAlpha (A:=itv) (WithTop.NotTop l1, h1) S1 ->
    IsAlpha (A:=itv) (l2, h2) S2 ->
    IsAlpha (A:=itv) (bound_mul l2 h1, bound_mul h2 h1)
      (collecting_binary_forward Z.mul S1 S2).
  Proof.
    move=> Hl1 Hnb1 Hl2 Hh2 Hex1 Hex2 Ha1 Ha2.
    have Hh1 : 0 ∈ γ[lubtop] h1.
    { have [c Hc] := proj1 (non_bottom_non_empty _) Hnb1.
      exact: (itv_gamma_lubtop_nonneg l1 c h1 Hl1 Hc). }
    apply: (interval_mul_pos_across_abstract l1 h1 l2 h2 S1 S2
              Hl1 Hnb1 Hl2 Hh2 Hex1 Hex2 Ha1 Ha2) => m p Hm Hp Hjoin.
    rewrite -(interval_mul_pos_across_join_eq l1 m p h1 l2 h2
                Hl1 Hm Hp Hl2 Hh2 Hh1).
    exact Hjoin.
  Qed.

  (** Closed-form α-completeness, negative (left) × across (right), both
      operand sets abstract. Derived from [interval_mul_pos_across_closed]
      by negating the left (negative) operand. *)
  Lemma interval_mul_neg_across_closed
    (l1 : WithTop.with_top Z) (h1 : Z) (l2 h2 : WithTop.with_top Z) (S1 S2 : ℘ Z) :
    h1 <= 0 -> non_bottom (l1, WithTop.NotTop h1) ->
    0 ∈ γ[glbtop] l2 -> 0 ∈ γ[lubtop] h2 ->
    (exists c, c ∈ S1) -> (exists c, c ∈ S2) ->
    IsAlpha (A:=itv) (l1, WithTop.NotTop h1) S1 ->
    IsAlpha (A:=itv) (l2, h2) S2 ->
    IsAlpha (A:=itv)
      (interval_opp (bound_mul l2 (neg_bound l1), bound_mul h2 (neg_bound l1)))
      (collecting_binary_forward Z.mul S1 S2).
  Proof.
    move=> Hh1 Hnb1 Hl2 Hh2 Hex1 Hex2 Ha1 Ha2.
    apply (is_alpha_opp_iff _ _).1 in Ha1.
    have Hnb1' : non_bottom (WithTop.NotTop (-h1), neg_bound l1)
      by case: l1 Hnb1 Ha1 => [_ | x Hx] _ /=; [done | move: Hx => /= Hx; lia].
    have Hex1' := opp_nonempty _ Hex1.
    have Hpos := interval_mul_pos_across_closed (-h1) (neg_bound l1) l2 h2
                   {[ z | -z ∈ S1 ]} S2
                   ltac:(lia) Hnb1' Hl2 Hh2 Hex1' Hex2 Ha1 Ha2.
    apply (is_alpha_opp_iff _ _).1 in Hpos.
    apply: (is_alpha_set_equiv _ _ _ _ Hpos).
    split=> z.
    - unfold_set => -[c2 [c1 [Hc2 [Hc1 Heq]]]]; unfold_set in Hc2.
      exists (-c2), c1; repeat split; [exact Hc2 | exact Hc1 | lia].
    - move=> [c2 [c1 [Hc2 [Hc1 <-]]]]; unfold_set.
      exists (-c2), c1; unfold_set; repeat split.
      + by replace (- - c2) with c2 by lia.
      + exact Hc1.
      + lia.
  Qed.

  (** Closed-form α-completeness, across × across, both operand sets
      abstract. Splits the LEFT operand at zero and combines the
      [neg×across] and [pos×across] closed forms via [is_alpha_join].
      Each half-result is independent of the split's interior bounds, so
      the join is already a closed form (the across×across result). *)
  Lemma interval_mul_across_across_closed
    (l1 h1 l2 h2 : WithTop.with_top Z) (S1 S2 : ℘ Z) :
    0 ∈ γ[glbtop] l1 -> 0 ∈ γ[lubtop] h1 ->
    0 ∈ γ[glbtop] l2 -> 0 ∈ γ[lubtop] h2 ->
    (exists c, c ∈ S1) -> (exists c, c ∈ S2) ->
    IsAlpha (A:=itv) (l1, h1) S1 ->
    IsAlpha (A:=itv) (l2, h2) S2 ->
    IsAlpha (A:=itv)
      (join_itv
         (interval_opp (bound_mul l2 (neg_bound l1), bound_mul h2 (neg_bound l1)))
         (bound_mul l2 h1, bound_mul h2 h1))
      (collecting_binary_forward Z.mul S1 S2).
  Proof.
    move=> Hl1 Hh1 Hl2 Hh2 Hex1 Hex2 Ha1 Ha2.
    move: (Ha1) => /Conjunction.is_alpha_pair_iff [Hglb1 Hlub1].
    apply: (itv_split_at_zero_alpha l1 h1 S1 Hl1 Hh1 Hex1 Ha1) => m p Hm Hp Han Hap.
    apply: (across_le0_witness l1 S1 Hl1 Hex1 Hglb1) => Hne_neg0.
    apply: (across_ge0_witness h1 S1 Hh1 Hex1 Hlub1) => Hne_pos0.
    have Hexn : exists c, c ∈ {[ z | z ∈ S1 /\ z <= 0 ]}
      by move: Hne_neg0 => [c [Hc Hc0]]; exists c; unfold_set; split.
    have Hexp : exists c, c ∈ {[ z | z ∈ S1 /\ 0 <= z ]}
      by move: Hne_pos0 => [c [Hc Hc0]]; exists c; unfold_set; split.
    have Hnbn : non_bottom (l1, WithTop.NotTop m).
    { apply/non_bottom_non_empty; move: Hexn => [c Hc].
      exists c; exact: (gamma_alpha_extensive itv _ _ Han c Hc). }
    have Hnbp : non_bottom (WithTop.NotTop p, h1).
    { apply/non_bottom_non_empty; move: Hexp => [c Hc].
      exists c; exact: (gamma_alpha_extensive itv _ _ Hap c Hc). }
    have Hn := interval_mul_neg_across_closed l1 m l2 h2
                 {[ z | z ∈ S1 /\ z <= 0 ]} S2
                 Hm Hnbn Hl2 Hh2 Hexn Hex2 Han Ha2.
    have Hpr := interval_mul_pos_across_closed p h1 l2 h2
                  {[ z | z ∈ S1 /\ 0 <= z ]} S2
                  Hp Hnbp Hl2 Hh2 Hexp Hex2 Hap Ha2.
    have HEQ :
      (collecting_binary_forward Z.mul {[ z | z ∈ S1 /\ z <= 0 ]} S2
       ∪ collecting_binary_forward Z.mul {[ z | z ∈ S1 /\ 0 <= z ]} S2)
      ⊆⊇ collecting_binary_forward Z.mul S1 S2.
    { split=> z; unfold_set.
      - move=> [ [c1 [c2 [Hc1 [Hc2 Heq]]]] | [c1 [c2 [Hc1 [Hc2 Heq]]]] ];
          move: Hc1; unfold_set => -[Hc1 _]; by exists c1, c2.
      - move=> [c1 [c2 [Hc1 [Hc2 Heq]]]].
        case: (Z.le_ge_cases c1 0) => Hsgn; [left | right];
          exists c1, c2; (repeat split) => //; unfold_set; by split. }
    exact: (is_alpha_join_split _ _ _ _ _ _ (symmetry HEQ) Hn Hpr).
  Qed.

  (** * Corrected interval multiplication with best abstraction.

      [interval_mul_opt] is the *extracted closed form*: a direct
      case split on the sign classification of both operands. Its
      best-abstraction proof is obtained via [interval_mul_math] below
      — a *proof-only* mirror whose branches are written in the same
      vocabulary as the per-quadrant [_best] lemmas — bridged by
      [interval_mul_math_eq]. Only [interval_mul_opt] is meant to be run
      / extracted; [interval_mul_math] never leaves the proofs. *)

  (** Extract Z value from a with_top bound, defaulting to 0 for Top. *)
  Definition extract_z (b : WithTop.with_top Z) : Z :=
    match b with WithTop.NotTop z => z | WithTop.Top => 0 end.

  (** Interval multiplication expressed in the "mathematical" vocabulary
      (to_high, mul_inf, high_inf, neg_bound, interval_opp, join_itv).
      Each branch directly matches the corresponding _best lemma statement. *)
  Definition interval_mul_math (i2 i1 : interval) : interval :=
    let (l1,h1) := i1 in
    let (l2,h2) := i2 in
    match classify i1, classify i2 with
    | Pos, Pos =>
        (WithTop.NotTop (extract_z l1 * extract_z l2),
         to_high (mul_inf (high_inf h1) (high_inf h2)))
    | Neg, Neg =>
        (WithTop.NotTop (extract_z h1 * extract_z h2),
         to_high (mul_inf (high_inf (neg_bound l1)) (high_inf (neg_bound l2))))
    | Neg, Pos =>
        interval_opp
          (WithTop.NotTop ((-extract_z h1) * extract_z l2),
           to_high (mul_inf (high_inf (neg_bound l1)) (high_inf h2)))
    | Pos, Neg =>
        interval_opp
          (WithTop.NotTop ((-extract_z h2) * extract_z l1),
           to_high (mul_inf (high_inf (neg_bound l2)) (high_inf h1)))
    | Pos, Across =>
        let l := extract_z l1 in
        join_itv
          (interval_opp
             (WithTop.NotTop (0 * l),
              to_high (mul_inf (high_inf (neg_bound l2)) (high_inf h1))))
          (WithTop.NotTop (l * 0),
           to_high (mul_inf (high_inf h1) (high_inf h2)))
    | Neg, Across =>
        let h := extract_z h1 in
        join_itv
          (WithTop.NotTop (h * 0),
           to_high (mul_inf (high_inf (neg_bound l1)) (high_inf (neg_bound l2))))
          (interval_opp
             (WithTop.NotTop ((-h) * 0),
              to_high (mul_inf (high_inf (neg_bound l1)) (high_inf h2))))
    | Across, Pos =>
        let l := extract_z l2 in
        join_itv
          (interval_opp
             (WithTop.NotTop (0 * l),
              to_high (mul_inf (high_inf (neg_bound l1)) (high_inf h2))))
          (WithTop.NotTop (l * 0),
           to_high (mul_inf (high_inf h2) (high_inf h1)))
    | Across, Neg =>
        let h := extract_z h2 in
        join_itv
          (WithTop.NotTop (h * 0),
           to_high (mul_inf (high_inf (neg_bound l2)) (high_inf (neg_bound l1))))
          (interval_opp
             (WithTop.NotTop ((-h) * 0),
              to_high (mul_inf (high_inf (neg_bound l2)) (high_inf h1))))
    | Across, Across =>
        join_itv
          (join_itv
             (WithTop.NotTop 0,
              to_high (mul_inf (high_inf (neg_bound l2)) (high_inf (neg_bound l1))))
             (interval_opp
                (WithTop.NotTop 0,
                 to_high (mul_inf (high_inf (neg_bound l2)) (high_inf h1)))))
          (join_itv
             (interval_opp
                (WithTop.NotTop 0,
                 to_high (mul_inf (high_inf (neg_bound l1)) (high_inf h2))))
             (WithTop.NotTop 0,
              to_high (mul_inf (high_inf h2) (high_inf h1))))
    end.

  (** * Equivalence between interval_mul_math and interval_mul_opt. *)

  Theorem interval_mul_math_eq : forall i2 i1,
    non_bottom i1 -> non_bottom i2 ->
    interval_mul_math i2 i1 = interval_mul_opt i2 i1.
  Proof.
    move=> [l2 h2] [l1 h1].
    case: l1 => [|[|l1|l1]]; case: h1 => [|[|h1|h1]];
       case: l2 => [|[|l2|l2]]; case: h2 => [|[|h2|h2]];
       rewrite /interval_mul_math /interval_mul_opt /join_itv
              /Conjunction.join /min_opt /max_opt
              /WithTop.lift2 /= => Hnb1 Hnb2 //;
       congr pair; congr (WithTop.NotTop); nia.
  Qed.

  (** * α-completeness for the full interval multiplication.

      Stronger than [interval_mul_*_best]: holds for arbitrary concrete
      sets [S2], [S1] (with [IsAlpha]), not just for [S = γ] of an
      interval. This is the form needed to compose multiplication with
      other domains (e.g. the reduced product). Analog of
      [interval_add_alpha_complete]; [interval_mul_opt_alpha_complete]
      follows as a corollary via [interval_mul_math_eq]. *)

  (** [bound_mul] is commutative. *)
  Lemma bound_mul_comm a b : bound_mul a b = bound_mul b a.
  Proof. by case: a => [|[|a|a]]; case: b => [|[|b|b]] //=; congr WithTop.NotTop; lia. Qed.

  (** Negating both operands of [bound_mul] cancels. *)
  Lemma bound_mul_neg_neg a b :
    bound_mul (neg_bound a) (neg_bound b) = bound_mul a b.
  Proof. by case: a => [|[|a|a]]; case: b => [|[|b|b]] //=; congr WithTop.NotTop; lia. Qed.

  (** α-completeness commutes through the (commutative) concrete product. *)
  Lemma alpha_mul_comm (a : itv) (S2 S1 : propset Z) :
    IsAlpha (A:=itv) a (collecting_binary_forward Z.mul S1 S2) ->
    IsAlpha (A:=itv) a (collecting_binary_forward Z.mul S2 S1).
  Proof. move=> H; apply: (IsAlpha_set_equiv _ _ _ _ H) => z; exact: collecting_mul_comm. Qed.

  (** Dispatches on the 3×3 sign classification. Sign cases apply the
      matching quadrant α-completeness directly (the [interval_mul_math] branch is the
      lemma's native form); across cases bridge to [interval_mul_opt]
      via [interval_mul_math_eq] and apply the closed-form across
      α-completeness, with [alpha_mul_comm] / [bound_mul] algebra fixing
      operand order. *)
  Lemma interval_mul_math_alpha_complete (i2 i1 : interval) (S2 S1 : propset Z) :
    non_bottom i1 -> non_bottom i2 ->
    (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
    binary_alpha_complete itv itv itv interval_mul_math
      (collecting_binary_forward Z.mul) i2 i1 S2 S1.
  Proof.
    move: i2 i1 => [l2 h2] [l1 h1] Hnb1 Hnb2 Hex2 Hex1.
    rewrite /binary_alpha_complete => Ha2 Ha1.
    case Hcl1: (classify (l1,h1)); case Hcl2: (classify (l2,h2)).
    (* Pos,Pos *)
    - move: (classify_Pos_inv _ _ Hcl1) => [l1' [Hl1e Hl1]].
      move: (classify_Pos_inv _ _ Hcl2) => [l2' [Hl2e Hl2]].
      subst l1 l2.
      rewrite /interval_mul_math Hcl1 Hcl2.
      exact: (interval_mul_pos_alpha_complete l1' l2' h1 h2 S2 S1
                Hl1 Hl2 Hnb1 Hnb2 Hex2 Hex1 Ha2 Ha1).
    (* Pos,Neg *)
    - move: (classify_Pos_inv _ _ Hcl1) => [l1' [Hl1e Hl1]].
      move: (classify_Neg_inv _ _ Hcl2) => [h2' [Hh2e Hh2]].
      subst l1 h2.
      rewrite /interval_mul_math Hcl1 Hcl2.
      apply: alpha_mul_comm.
      exact: (interval_mul_neg_pos_alpha_complete l1' h1 l2 h2' S1 S2
                Hl1 Hh2 Hnb1 Hnb2 Hex1 Hex2 Ha1 Ha2).
    (* Pos,Across *)
    - move: (classify_Pos_inv _ _ Hcl1) => [l1' [Hl1e Hl1]].
      subst l1.
      have [Hl2z Hh2z] := classify_Across_inv _ _ Hnb2 Hcl2.
      rewrite (interval_mul_math_eq (l2,h2) (WithTop.NotTop l1',h1) Hnb1 Hnb2)
              /interval_mul_opt Hcl1 Hcl2.
      rewrite (bound_mul_comm h1 l2) (bound_mul_comm h1 h2).
      apply: alpha_mul_comm.
      exact: (interval_mul_pos_across_closed l1' h1 l2 h2 S1 S2
                Hl1 Hnb1 Hl2z Hh2z Hex1 Hex2 Ha1 Ha2).
    (* Neg,Pos *)
    - move: (classify_Neg_inv _ _ Hcl1) => [h1' [Hh1e Hh1]].
      move: (classify_Pos_inv _ _ Hcl2) => [l2' [Hl2e Hl2]].
      subst h1 l2.
      rewrite /interval_mul_math Hcl1 Hcl2.
      exact: (interval_mul_neg_pos_alpha_complete l2' h2 l1 h1' S2 S1
                Hl2 Hh1 Hnb2 Hnb1 Hex2 Hex1 Ha2 Ha1).
    (* Neg,Neg *)
    - move: (classify_Neg_inv _ _ Hcl1) => [h1' [Hh1e Hh1]].
      move: (classify_Neg_inv _ _ Hcl2) => [h2' [Hh2e Hh2]].
      subst h1 h2.
      rewrite /interval_mul_math Hcl1 Hcl2 /=.
      replace (h1' * h2') with (- h1' * - h2') by ring.
      exact: (interval_mul_neg_neg_alpha_complete l2 l1 h2' h1' S2 S1
                Hh2 Hh1 Hnb2 Hnb1 Hex2 Hex1 Ha2 Ha1).
    (* Neg,Across *)
    - move: (classify_Neg_inv _ _ Hcl1) => [h1' [Hh1e Hh1]].
      subst h1.
      have [Hl2z Hh2z] := classify_Across_inv _ _ Hnb2 Hcl2.
      rewrite (interval_mul_math_eq (l2,h2) (l1,WithTop.NotTop h1') Hnb1 Hnb2)
              /interval_mul_opt Hcl1 Hcl2.
      apply: alpha_mul_comm.
      have ->: (bound_mul l1 h2, bound_mul l1 l2)
             = interval_opp (bound_mul l2 (neg_bound l1), bound_mul h2 (neg_bound l1)).
      { rewrite /interval_opp !bound_mul_neg_l !bound_mul_neg_neg
                (bound_mul_comm h2 l1) (bound_mul_comm l2 l1). by []. }
      exact: (interval_mul_neg_across_closed l1 h1' l2 h2 S1 S2
                Hh1 Hnb1 Hl2z Hh2z Hex1 Hex2 Ha1 Ha2).
    (* Across,Pos *)
    - move: (classify_Pos_inv _ _ Hcl2) => [l2' [Hl2e Hl2]].
      subst l2.
      have [Hl1z Hh1z] := classify_Across_inv _ _ Hnb1 Hcl1.
      rewrite (interval_mul_math_eq (WithTop.NotTop l2',h2) (l1,h1) Hnb1 Hnb2)
              /interval_mul_opt Hcl1 Hcl2.
      exact: (interval_mul_pos_across_closed l2' h2 l1 h1 S2 S1
                Hl2 Hnb2 Hl1z Hh1z Hex2 Hex1 Ha2 Ha1).
    (* Across,Neg *)
    - move: (classify_Neg_inv _ _ Hcl2) => [h2' [Hh2e Hh2]].
      subst h2.
      have [Hl1z Hh1z] := classify_Across_inv _ _ Hnb1 Hcl1.
      rewrite (interval_mul_math_eq (l2,WithTop.NotTop h2') (l1,h1) Hnb1 Hnb2)
              /interval_mul_opt Hcl1 Hcl2.
      have ->: (bound_mul h1 l2, bound_mul l1 l2)
             = interval_opp (bound_mul l1 (neg_bound l2), bound_mul h1 (neg_bound l2)).
      { rewrite /interval_opp !bound_mul_neg_l !bound_mul_neg_neg. by []. }
      exact: (interval_mul_neg_across_closed l2 h2' l1 h1 S2 S1
                Hh2 Hnb2 Hl1z Hh1z Hex2 Hex1 Ha2 Ha1).
    (* Across,Across *)
    - have [Hl1z Hh1z] := classify_Across_inv _ _ Hnb1 Hcl1.
      have [Hl2z Hh2z] := classify_Across_inv _ _ Hnb2 Hcl2.
      rewrite (interval_mul_math_eq (l2,h2) (l1,h1) Hnb1 Hnb2)
              /interval_mul_opt Hcl1 Hcl2.
      apply: alpha_mul_comm.
      have ->: (min_opt (bound_mul l1 h2) (bound_mul h1 l2),
                max_opt (bound_mul l1 l2) (bound_mul h1 h2))
             = join_itv (interval_opp (bound_mul l2 (neg_bound l1), bound_mul h2 (neg_bound l1)))
                        (bound_mul l2 h1, bound_mul h2 h1).
      { rewrite /join_itv /Conjunction.join /interval_opp
                !bound_mul_neg_l !bound_mul_neg_neg
                (bound_mul_comm h2 l1) (bound_mul_comm l2 h1)
                (bound_mul_comm l2 l1) (bound_mul_comm h2 h1). by []. }
      exact: (interval_mul_across_across_closed l1 h1 l2 h2 S1 S2
                Hl1z Hh1z Hl2z Hh2z Hex1 Hex2 Ha1 Ha2).
  Qed.

  (** Closed-form variant: α-completeness for [interval_mul_opt]. *)
  Lemma interval_mul_opt_alpha_complete (i2 i1 : interval) (S2 S1 : propset Z) :
    non_bottom i1 -> non_bottom i2 ->
    (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
    binary_alpha_complete itv itv itv interval_mul_opt
      (collecting_binary_forward Z.mul) i2 i1 S2 S1.
  Proof.
    move=> Hnb1 Hnb2 Hex2 Hex1.
    rewrite /binary_alpha_complete -(interval_mul_math_eq i2 i1 Hnb1 Hnb2) => Ha2 Ha1.
    exact: (interval_mul_math_alpha_complete i2 i1 S2 S1 Hnb1 Hnb2 Hex2 Hex1 Ha2 Ha1).
  Qed.

  (** [interval_mul_opt] is the best abstraction, derived directly
      from α-completeness via [binary_alpha_complete_to_best] (operands
      are maximally reduced since non-bottom). *)
  Theorem interval_mul_opt_best i2 i1 :
    non_bottom i1 -> non_bottom i2 ->
    BestAbstraction (A:=itv) (interval_mul_opt i2 i1)
      (collecting_binary_forward Z.mul (γ[itv] i2) (γ[itv] i1)).
  Proof.
    move=> Hnb1 Hnb2.
    have MR2 := non_bottom_MaximallyReduced _ Hnb2.
    have MR1 := non_bottom_MaximallyReduced _ Hnb1.
    have /non_bottom_non_empty Hex2 := Hnb2.
    have /non_bottom_non_empty Hex1 := Hnb1.
    exact: (binary_alpha_complete_to_best itv itv itv interval_mul_opt
              _ _ _
              (interval_mul_opt_alpha_complete i2 i1 _ _ Hnb1 Hnb2 Hex2 Hex1)).
  Qed.

End Interval_mul.
