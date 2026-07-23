(* STATUS: the congruence domain  (r, m) ↦ { z | m | z - r }.
   order : exact (ExactOrder)          join : least upper bound (cong_ajsl, cong_join_is_lub)

   All transfer functions now live in Transfer_function/Congruence/; what is
   left here is the abstraction itself plus the shared γ / carry helpers.
   add  (Z.add)  : sound + exact + α-complete  AddTheory.v
   opp  (Z.opp)  : exact                       AddTheory.v
   sub  (Z.sub)  : exact                       AddTheory.v
   mul  (Z.mul)  : sound + best, NOT γ-exact  MulTheory.v
   div  (Z.div)  : best, exact in A/B/D1  DivTheory.v
   quot (Z.quot) : best                 QuotTheory.v
   le   (Z.leb)  : exact + best         LeTheory.v
   eqb  (Z.eqb)  : exact + best         EqbTheory.v *)

Require Import Abstraction AbstractLattice.
Require Import ssreflect ssrbool ssrfun.
Require Import BoundAbstraction.
Require Import AbstractionCombination.
Require Import BoundLattice.
Require Import autoreflect.
Require Import Tactics.
Require Import Stdlib.Bool.Bool.
Require Import Quadrivalent.
(* From Hammer Require Import Hammer. *)
From Stdlib Require Import Lia. (* lia/nia; avoid Psatz which loads Reals axioms *)
Require Import ZCongruence.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory.
Open Scope Z_scope.             (* Arithmetic operations are all on Z; avoids %Z everywhere. *)
Generalizable All Variables.


From Stdlib Require Export Setoid.
From Stdlib Require Export Classes.Morphisms.
From Stdlib Require Export Morphisms.


(* The idea: we will reuse our boundlattice machinery, by defining a
   concrete order on pairs of values, finding the correct lcm and gcd.

   What we won't have is unbounded things, or two bounds, so things
   should actually be quite simple. We can prove that (0,1) is an
   lower bound (top). We don't have bottom.

   We also won't have unicity (injectivity), unless we require it
   (e.g. we can ask that divisor is positive, and rest between 0 and
   it). No need for most proofs I think; but we could be proving that
   our transfer functions have this invariant.

   What is nice is that we can have an equiv variant that would not
   need that. It suffices to show that dividors are the same or
   opposite, and the rests are multiple of that divisor.

   Asking the divisor to be positive is probably best.

   This is nice because it allows exposing the various implementation
   options.

   The use of preorder instead of complete order (without
   antisymmetry) is nice here. Something to say in the text.

 *)

(* Follows granger definition. The order is aligned with the ⊑ and ⊑γ
   ordering; i.e. smaller multiples represent a larger set of
   numbers. *)
Definition order (a b: zcongruence) :=
  let (ra,ma) := a in
  let (rb,mb) := b in   
  Z.divide mb ma /\ Z.divide mb (ra - rb).

Lemma order_preorder: PreOrder order.
Proof.
  constructor.
  - move => [r m]. rewrite /order; split.
    + reflexivity.
    + replace (r-r) with 0 by lia. apply Z.divide_0_r.
  - move => [rx mx] [ry my] [rz mz]; rewrite /order; move => [Hmxy Hrxy] [Hmyz Hryz]; split.
    + by transitivity my.
    + have H: (mz | rx - ry) by transitivity my.
      replace (rx - rz) with ((rx - ry) + (ry - rz)).
      * by apply: Z.divide_add_r.
      * by lia.
Qed.




(** (0,1) is the maximal (top) element: every pair is below it. *)
Lemma order_top a : order a (0, 1).
Proof.
  destruct a as [r m]. rewrite /order. split.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
Qed.

(** (r,0) elements are minimal: the only element below (r,0) is itself. *)
Lemma order_minimal r r' m' : order (r', m') (r, 0) -> r' = r /\ m' = 0.
Proof.
  rewrite /order. move=> [[k Hk] [j Hj]].
  split; lia.
Qed.

(** [order] is decidable: it is a conjunction of divisibility tests. *)
Lemma order_dec a b : {order a b} + {~ order a b}.
Proof.
  move: a b => [ra ma] [rb mb]. rewrite /order.
  case: (Zdivide_dec mb ma) => Hd1; last by right; tauto.
  case: (Zdivide_dec mb (ra - rb)) => Hd2; last by right;tauto.
  by left.
Qed.

(** Hence [order] goals are [¬¬]-stable. *)
Global Instance order_stable a b : Stable (order a b) :=
  dec_stable (order_dec a b).

(** * Concretization. *)

(** γ(r,m) = {z ∈ Z | m divides (z - r)}.
    When m = 0, Z.divide 0 x iff x = 0, so γ(r,0) = {r}. *)
Definition cong_gamma (a : zcongruence) : ℘ Z :=
  let (r, m) := a in {[ z | (m | (z - r)) ]}.

Definition cong_abs : abstraction Z := BuildAbstraction cong_gamma.

(** * Abstract domain. *)

Existing Instance order_preorder.

Program Instance cong_ad_laws :
  abstract_domain_laws (A:=cong_abs) cong_gamma order.
Next Obligation.
  (* OrderPreserving cong_gamma order propset_subseteq *)
  move=> [r1 m1] [r2 m2] [Hm Hr] z. unfold_set.
  move=> Hz.
  replace (z - r2) with ((z - r1) + (r1 - r2)) by lia.
  apply Z.divide_add_r; [by transitivity m1 | done].
Qed.

Definition cong_ad : abstract_domain Z :=
  BuildAbstractDomain cong_gamma order cong_ad_laws.
Global Hint Unfold cong_ad cong_gamma : unfold_gamma.

(** * ExactOrder. *)

Instance cong_exact_order : ExactOrder cong_ad.
Proof.
  move=> [r1 m1] [r2 m2]. split.
  - apply sound_order.
  - unfold_set; simpl; unfold_set.
    move=> H. split.
    + (* m2 | m1 *)
      replace m1 with ((r1 + m1 - r2) - (r1 - r2)) by lia.
      apply Z.divide_sub_r.
      * apply H. exists 1. lia.
      * apply H. exists 0. lia.
    + (* m2 | (r1 - r2) *)
      apply H. exists 0. lia.
Qed.

(** * γ is never empty. *)

(** Every congruence class is inhabited: r ∈ γ(r, m). *)
Lemma gamma_non_empty (a : zcongruence) : exists z, z ∈ γ[cong_ad] a.
Proof.
  destruct a as [r m]. exists r. simpl. unfold_set.
  exists 0. lia.
Qed.

(** γ(r, 0) = {r}: the only element of a singleton congruence class is r. *)
Lemma gamma_singleton c r : c ∈ γ[cong_ad] (r, 0) <-> c = r.
Proof.
  split.
  - unfold_set. by case=> k; lia.
  - move=> ->. unfold_set. by exists 0; lia.
Qed.

(** [is_singleton c = Some x] exactly when [γ c] is the singleton [{x}].
    The [None] case covers every non-singleton class — one with at least
    two elements (for a congruence, in fact an infinite progression, as
    [γ] is never empty). *)
Lemma is_singleton_spec (c : zcongruence) (x : Z) :
  is_singleton c = Some x <-> (forall z, z ∈ γ[cong_ad] c <-> z = x).
Proof.
  destruct c as [r m]. unfold is_singleton. split.
  - destruct (Z.eqb m 0) eqn:Hm; [| discriminate].
    apply Z.eqb_eq in Hm. subst m.
    move=> H. injection H as Heq. subst x.
    move=> z. exact: gamma_singleton.
  - move=> Hchar.
    have Hr : r ∈ γ[cong_ad] (r, m) by simpl; unfold_set; exists 0; lia.
    have Hrx : r = x := proj1 (Hchar r) Hr.
    have Hm0 : m = 0.
    { have Hrm : (r + m) ∈ γ[cong_ad] (r, m) by simpl; unfold_set; exists 1; lia.
      have Hrmx : r + m = x := proj1 (Hchar (r + m)) Hrm. lia. }
    subst m. simpl. by rewrite Hrx.
Qed.

(** There is no best abstraction of the empty set: given any (r,m),
    (r+1,0) is also an overapproximation of ∅, but (r,m) ⊑ (r+1,0)
    leads to 0 | -1, a contradiction. *)
Lemma alpha_non_empty a S:
  IsAlpha (A:=cong_ad) a S ->
  (forall z, ~(z ∈ S)) -> False.
Proof.
  destruct a as [r m].
  rewrite is_alpha_iff_best_abstraction.
  move=> [Hsound Hopt] Hempty.
  have Hsub: Overapproximates (A:=cong_ad) (r + 1, 0) S.
  { move=> z Hz. exfalso. by apply Hempty in Hz. }
  move: (Hopt _ Hsub).
  move=> [_ [k Hk]]. lia.
Qed.

(** Extract a concrete witness of a non-empty abstracted set: to prove
    any [¬¬]-stable goal [G], one may assume [∃z, z ∈ S]. The witness
    cannot be produced unconditionally (that would need classical
    logic), but it is available when the goal is stable. *)
Lemma alpha_non_empty_witness {G : Prop} `{Stable G} (a : zcongruence) (S : ℘ Z) :
  IsAlpha (A:=cong_ad) a S -> ((exists z, z ∈ S) -> G) -> G.
Proof.
  move=> Ha Hf. apply: stable => Hng.
  apply: (alpha_non_empty a S Ha) => z Hz.
  by apply/Hng/Hf; exists z.
Qed.

(** * LUB layer (proof machinery). *)

Definition lub_ad : abstract_domain zcongruence :=
  BoundAbstraction.LUB.ad order.

(** * StrongAlphaRelation via LUB layer. *)

(** Embed integers into congruence pairs: z ↦ (z, 0). *)
Definition singleton_embed (S : propset Z) : propset zcongruence :=
  {[ p | exists z, z ∈ S /\ p = (z, 0) ]}.

(** The key bijection: (z, 0) ≤ (r, m) ⟺ z ∈ γ(r, m). *)
Lemma singleton_order_gamma z r m :
  order (z, 0) (r, m) <-> z ∈ γ[cong_ad] (r, m).
Proof.
  rewrite /order. simpl. unfold_set. split.
  - move=> [_ H]. done.
  - move=> H. split; [apply Z.divide_0_r | done].
Qed.

(** Lifting: membership in γ[lub_ad] via singleton_embed
    is the same as membership in γ[cong_ad]. *)
Lemma singleton_embed_sub_gamma (S : propset Z) (a : zcongruence) :
  singleton_embed S ⊆ γ[lub_ad] a <-> S ⊆ γ[cong_ad] a.
Proof.
  destruct a as [r m]. split.
  - move=> Hsub z Hz.
    have := Hsub (z, 0) (ex_intro _ z (conj Hz eq_refl)).
    simpl. unfold_set. rewrite /order. move=> [_ H]. done.
  - move=> Hsub [rz mz] [z [Hz Heq]].
    injection Heq => -> ->.
    simpl. unfold_set. rewrite /order. split.
    + apply Z.divide_0_r.
    + exact (Hsub z Hz).
Qed.

(** IsAlpha on the LUB layer (for singleton-embedded sets)
    is equivalent to IsAlpha on the direct layer. *)
Lemma is_alpha_lub_cong (a : zcongruence) (S : propset Z) :
  IsAlpha (A:=lub_ad) a (singleton_embed S) <-> IsAlpha (A:=cong_ad) a S.
Proof.
  split.
  - move=> Hadj_lub a'. rewrite -singleton_embed_sub_gamma. apply Hadj_lub.
  - move=> Hadj_cong a'. rewrite singleton_embed_sub_gamma. apply Hadj_cong.
Qed.

(** * Join operation. *)

(** Equivalence: two congruence pairs represent the same set. *)
Definition cong_equiv (a1 a2 : zcongruence) : Prop :=
  order a1 a2 /\ order a2 a1.

Lemma conv_equiv1 (a1 a2 : zcongruence) :
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  cong_equiv a1 a2 ->
  m1 = m2 \/ m1 = - m2.
Proof.
  move: a1 a2 => [r1 m1] [r2 m2] [[Hll _] [Hrr _]]. 
  unfold order in *.
  have H:= (Z.divide_antisym_abs _ _ Hll Hrr).
  lia.
Qed.

Lemma cong_join_compat_l a1 a2 : order a1 (cong_join a1 a2).
Proof.
  destruct a1 as [r1 m1], a2 as [r2 m2]. rewrite /cong_join /order. split.
  - transitivity (Z.gcd m1 m2).
    + apply Z.gcd_divide_l.
    + apply Z.gcd_divide_l.
  - replace (r1 - r1) with 0 by lia. apply Z.divide_0_r.
Qed.

Lemma cong_join_compat_r a1 a2 : order a2 (cong_join a1 a2).
Proof.
  destruct a1 as [r1 m1], a2 as [r2 m2]. rewrite /cong_join /order. split.
  - transitivity (Z.gcd m1 m2).
    + apply Z.gcd_divide_l.
    + apply Z.gcd_divide_r.
  - apply Z.divide_opp_r. replace (- (r2 - r1)) with (r1 - r2) by lia.
    apply Z.gcd_divide_r.
Qed.

Instance cong_ajsl_laws :
  abstract_join_semilattice_laws cong_ad cong_join cong_equiv.
Proof.
  constructor.
  - exact cong_ad_laws.
  - move=> a1 a2 [H1 H2]. split; done.
  - apply cong_join_compat_l.
  - apply cong_join_compat_r.
Qed.

Definition cong_ajsl : abstract_join_semilattice Z :=
  BuildAbstractJoinSemilattice cong_ad cong_join cong_equiv cong_ajsl_laws.

(** Join is a true LUB: if a1 ⊑ c and a2 ⊑ c, then join(a1,a2) ⊑ c. *)
Instance cong_join_is_lub : JoinIsLUB cong_ajsl.
Proof.
  move=> [r1 m1] [r2 m2] [rc mc]. rewrite /= /order.
  move=> [Hmc_m1 Hmc_r1] [Hmc_m2 Hmc_r2]. split.
  - apply Z.gcd_greatest.
    + apply Z.gcd_greatest; done.
    + replace (r1 - r2) with ((r1 - rc) - (r2 - rc)) by lia.
      apply Z.divide_sub_r; done.
  - done.
Qed.

(** The strong α relation for cong_ad, derived from LUB.is_lub. *)

(* The strong α relation is obtained from the LUB machinery: α(S) is the
   least upper bound of the singleton embedding of S. Since cong_ad has
   ExactOrder, this coincides with MostPrecise; we phrase it as an LUB
   because the bound form is more convenient in the precision proofs. *)
Program Instance cong_strong_alpha : StrongAlphaRelation cong_ad :=
  {| strong_α_relation (a : zcongruence) (S : propset Z) :=
       BoundAbstraction.LUB.is_lub order a (singleton_embed S) |}.
Next Obligation.
  (* is_lub ⟺ IsAlpha(lub_ad) ⟺ IsAlpha(cong_ad) *)
  split.
  - move=> Hlub. apply is_alpha_lub_cong.
    by apply (strong_α_relation_spec (StrongAlphaRelation:=BoundAbstraction.LUB.galois order)).
  - move=> Hadj. apply (strong_α_relation_spec (StrongAlphaRelation:=BoundAbstraction.LUB.galois order)).
    by apply is_alpha_lub_cong.
Qed.



(** * Carry/pigeonhole helpers for division progressions.

    Generic [Z.div] carry facts shared by the [Z.div] and [Z.quot] transfer
    functions ([Transfer_function/Congruence/DivTheory.v], [.../QuotTheory.v]),
    so they stay in the abstraction layer rather than in either operation. *)

(** Carry identity for Z.div: splitting the numerator yields a unit carry
    depending on whether the remainders overflow c. *)
Lemma Z_div_add_carry a b c :
  0 < c ->
  (a + b) / c = a / c + b / c
              + (if (a mod c + b mod c) <? c then 0 else 1).
Proof.
  move=> Hc.
  have Hne : c <> 0 by lia.
  have := Z.mod_pos_bound a c Hc.
  have := Z.mod_pos_bound b c Hc.
  have := Z.div_mod a c Hne.
  have := Z.div_mod b c Hne.
  case: (Z.ltb_spec (a mod c + b mod c) c) => Hcar.
  - rewrite Z.add_0_r.
    symmetry. apply: (Z.div_unique _ _ _ (a mod c + b mod c)); lia.
  - symmetry. apply: (Z.div_unique _ _ _ (a mod c + b mod c - c)); lia.
Qed.

(** Constructive existence of a no-carry step. If the total division
    growth after N steps stays strictly below N·(q+1), at least one of
    those steps must have carry = 0. We find it by induction. *)
Lemma exists_no_carry_step r1 m1 r2 :
  0 < r2 -> forall N, 0 <= N ->
  (r1 + N*m1) / r2 - r1 / r2 < N * (m1 / r2 + 1) ->
  exists k, 0 <= k < N /\ (r1 + k*m1) mod r2 + m1 mod r2 < r2.
Proof.
  move=> Hr2. apply: natlike_ind => [Hc|N HN IH Hbound].
  - exfalso.
    have Heq : r1 + 0*m1 = r1 by ring.
    rewrite Heq in Hc. lia.
  - case: (Z.ltb_spec ((r1 + N*m1) mod r2 + m1 mod r2) r2) => Hstep.
    + (* no carry at step N: take k = N *)
      by exists N; split; [lia | exact Hstep].
    + (* carry at step N: reduce hypothesis to IH's form *)
      have Heq : (r1 + Z.succ N * m1) / r2 = (r1 + N*m1) / r2 + m1 / r2 + 1.
      { have -> : r1 + Z.succ N * m1 = (r1 + N*m1) + m1 by ring.
        rewrite Z_div_add_carry //.
        have -> : ((r1 + N*m1) mod r2 + m1 mod r2 <? r2) = false
          by apply/Z.ltb_ge; lia.
        lia. }
      have Hbound' : (r1 + N*m1) / r2 - r1 / r2 < N * (m1/r2 + 1) by lia.
      have [k [Hk Hnc]] := IH Hbound'.
      by exists k; split; [lia | exact Hnc].
Qed.

(** Constructive existence of a carry step (symmetric). *)
Lemma exists_carry_step r1 m1 r2 :
  0 < r2 -> forall N, 0 <= N ->
  N * (m1 / r2) < (r1 + N*m1) / r2 - r1 / r2 ->
  exists k, 0 <= k < N /\ r2 <= (r1 + k*m1) mod r2 + m1 mod r2.
Proof.
  move=> Hr2. apply: natlike_ind => [Hc|N HN IH Hbound].
  - exfalso.
    have Heq : r1 + 0*m1 = r1 by ring.
    rewrite Heq in Hc. lia.
  - case: (Z.ltb_spec ((r1 + N*m1) mod r2 + m1 mod r2) r2) => Hstep.
    + (* no carry at N: reduce to IH *)
      have Heq : (r1 + Z.succ N * m1) / r2 = (r1 + N*m1) / r2 + m1 / r2.
      { have -> : r1 + Z.succ N * m1 = (r1 + N*m1) + m1 by ring.
        rewrite Z_div_add_carry //.
        have -> : ((r1 + N*m1) mod r2 + m1 mod r2 <? r2) = true
          by apply/Z.ltb_lt; lia.
        lia. }
      have Hbound' : N * (m1/r2) < (r1 + N*m1) / r2 - r1/r2 by lia.
      have [k [Hk Hc]] := IH Hbound'.
      by exists k; split; [lia | exact Hc].
    + (* carry at N: take k = N *)
      by exists N; split; [lia | exact Hstep].
Qed.

(** Core carry argument, parametric over which divisions (Z.div vs
    Z.quot). Given that every [V(k) = Z.div (r1+k·m1) r2] for [k ∈ [0, r2]]
    satisfies [m' ∣ V(k) − r'], and the divisor doesn't divide the step,
    we conclude [m' ∣ 1]. *)
Lemma carry_witnesses_divides_one r1 m1 r2 r' m' :
  0 < r2 -> ~(r2 | m1) ->
  (forall k, 0 <= k <= r2 -> (m' | Z.div (r1 + k*m1) r2 - r')) ->
  (m' | 1).
Proof.
  move=> Hr2 Hnd V_in.
  have Hr2_ne : r2 <> 0 by lia.
  have Hrm : 0 < m1 mod r2 < r2.
  { have := Z.mod_pos_bound m1 r2 Hr2.
    case: (Z.eq_dec (m1 mod r2) 0) => [Heq|Hne0]; [|lia].
    exfalso; apply: Hnd. by apply (proj1 (Z.mod_divide _ _ Hr2_ne)). }
  have gap_div : forall k, 0 <= k < r2 ->
    (m' | (r1 + (k+1)*m1) / r2 - (r1 + k*m1) / r2).
  { move=> k Hk.
    have -> : (r1 + (k+1)*m1) / r2 - (r1 + k*m1) / r2 =
              ((r1 + (k+1)*m1) / r2 - r') - ((r1 + k*m1) / r2 - r') by ring.
    apply: Z.divide_sub_r; apply: V_in; lia. }
  set q := m1 / r2.
  have gap_eq : forall k,
    (r1 + (k+1)*m1) / r2 - (r1 + k*m1) / r2 =
      q + (if (r1 + k*m1) mod r2 + m1 mod r2 <? r2 then 0 else 1).
  { move=> k. have -> : r1 + (k+1)*m1 = (r1 + k*m1) + m1 by ring.
    rewrite Z_div_add_carry //. lia. }
  have Hf_r2 : (r1 + r2*m1) / r2 - r1 / r2 = m1.
  { have -> : r1 + r2*m1 = r1 + m1*r2 by ring.
    rewrite (Z.div_add _ _ _ Hr2_ne). lia. }
  have Hm1 : m1 = r2 * q + m1 mod r2.
  { rewrite /q. exact: Z.div_mod _ _ Hr2_ne. }
  have Hq : (m' | q).
  { have Hbound : (r1 + r2*m1) / r2 - r1 / r2 < r2 * (q + 1).
    { rewrite Hf_r2. nia. }
    have [k [Hk Hnc]] := exists_no_carry_step r1 m1 r2 Hr2 r2 ltac:(lia) Hbound.
    have Hgd := gap_div k ltac:(lia). rewrite gap_eq in Hgd.
    have Hbb : ((r1 + k*m1) mod r2 + m1 mod r2 <? r2) = true
      by apply/Z.ltb_lt; exact Hnc.
    by rewrite Hbb Z.add_0_r in Hgd. }
  have Hq1 : (m' | q + 1).
  { have Hbound : r2 * q < (r1 + r2*m1) / r2 - r1 / r2.
    { rewrite Hf_r2. nia. }
    have [k [Hk Hc]] := exists_carry_step r1 m1 r2 Hr2 r2 ltac:(lia) Hbound.
    have Hgd := gap_div k ltac:(lia). rewrite gap_eq in Hgd.
    have Hbb : ((r1 + k*m1) mod r2 + m1 mod r2 <? r2) = false
      by apply/Z.ltb_ge; exact Hc.
    by rewrite Hbb in Hgd. }
  replace 1 with ((q + 1) - q) by lia.
  exact: Z.divide_sub_r Hq1 Hq.
Qed.


(** * Unboundedness of γ.

    Progression / unboundedness facts about γ(r, m), used by the
    comparison transfer functions ([cong_le], [cong_eqb]). *)

(** Helper: every [r + k·|m|] lies in [γ(r, m)]. *)
Lemma cong_in_progression r m k :
  r + k * Z.abs m ∈ γ[cong_ad] (r, m).
Proof.
  unfold_set. exists (k * Z.sgn m).
  have := Z.abs_sgn m. nia.
Qed.

(** When [m ≠ 0], [γ(r, m)] is unbounded above and below. *)
Lemma cong_unbounded_above r m N :
  m <> 0 -> exists z, z ∈ γ[cong_ad] (r, m) /\ N <= z.
Proof.
  move=> Hm.
  pose k := Z.abs (N - r) + 1.
  exists (r + k * Z.abs m). split; first exact: cong_in_progression.
  have Hm_pos : 1 <= Z.abs m by case: (Z.abs_spec m); lia.
  have Habs_ge : N - r <= Z.abs (N - r) by case: (Z.abs_spec (N - r)); lia.
  rewrite /k. nia.
Qed.

Lemma cong_unbounded_below r m N :
  m <> 0 -> exists z, z ∈ γ[cong_ad] (r, m) /\ z <= N.
Proof.
  move=> Hm.
  pose k := - (Z.abs (N - r) + 1).
  exists (r + k * Z.abs m). split; first exact: cong_in_progression.
  have Hm_pos : 1 <= Z.abs m by case: (Z.abs_spec m); lia.
  have Habs_ge : -(N - r) <= Z.abs (N - r) by case: (Z.abs_spec (N - r)); lia.
  rewrite /k. nia.
Qed.
