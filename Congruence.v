(* STATUS: the congruence domain  (r, m) ↦ { z | m | z - r }.
   order : exact (ExactOrder)          join : least upper bound (cong_ajsl, cong_join_is_lub)
   add   : sound + exact + α-complete   (cong_add_sound / _exact / _alpha_complete)
   opp   : exact                        sub  : exact            (cong_opp_* , cong_sub_* )
   mul   : sound + best, NOT γ-exact    (cong_mul_sound / _best / _not_gamma_exact)
   div  (Z.div)  : best — exact in cases A/B/D1    (cong_div_best)
   quot (Z.quot) : best                             (cong_quot_best)
   le   (Z.leb)  : exact + best         (cong_le_exact / cong_le_best)

   Transfer functions already split out into Transfer_function/Congruence/:
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
Definition order (a b: Z * Z) :=
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
Definition cong_gamma (a : Z * Z) : ℘ Z :=
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
Lemma gamma_non_empty (a : Z * Z) : exists z, z ∈ γ[cong_ad] a.
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
Lemma alpha_non_empty_witness {G : Prop} `{Stable G} (a : Z * Z) (S : ℘ Z) :
  IsAlpha (A:=cong_ad) a S -> ((exists z, z ∈ S) -> G) -> G.
Proof.
  move=> Ha Hf. apply: stable => Hng.
  apply: (alpha_non_empty a S Ha) => z Hz.
  by apply/Hng/Hf; exists z.
Qed.

(** * LUB layer (proof machinery). *)

Definition lub_ad : abstract_domain (Z * Z) :=
  BoundAbstraction.LUB.ad order.

(** * StrongAlphaRelation via LUB layer. *)

(** Embed integers into congruence pairs: z ↦ (z, 0). *)
Definition singleton_embed (S : propset Z) : propset (Z * Z) :=
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
Lemma singleton_embed_sub_gamma (S : propset Z) (a : Z * Z) :
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
Lemma is_alpha_lub_cong (a : Z * Z) (S : propset Z) :
  IsAlpha (A:=lub_ad) a (singleton_embed S) <-> IsAlpha (A:=cong_ad) a S.
Proof.
  split.
  - move=> Hadj_lub a'. rewrite -singleton_embed_sub_gamma. apply Hadj_lub.
  - move=> Hadj_cong a'. rewrite singleton_embed_sub_gamma. apply Hadj_cong.
Qed.

(** * Join operation. *)

(** The join of two congruence classes γ(r1,m1) and γ(r2,m2) is the
    smallest congruence class containing both: (r1, gcd(gcd(m1,m2), r1-r2)).
    The modulus is the gcd of both moduli and the difference of remainders,
    and the remainder is r1 (arbitrary choice; r2 works equally). *)

Definition cong_join (a1 a2 : Z * Z) : Z * Z :=
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  (r1, Z.gcd (Z.gcd m1 m2) (r1 - r2)).

(** Equivalence: two congruence pairs represent the same set. *)
Definition cong_equiv (a1 a2 : Z * Z) : Prop :=
  order a1 a2 /\ order a2 a1.

Lemma conv_equiv1 (a1 a2 : Z * Z) :
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
  {| strong_α_relation (a : Z * Z) (S : propset Z) :=
       BoundAbstraction.LUB.is_lub order a (singleton_embed S) |}.
Next Obligation.
  (* is_lub ⟺ IsAlpha(lub_ad) ⟺ IsAlpha(cong_ad) *)
  split.
  - move=> Hlub. apply is_alpha_lub_cong.
    by apply (strong_α_relation_spec (StrongAlphaRelation:=BoundAbstraction.LUB.galois order)).
  - move=> Hadj. apply (strong_α_relation_spec (StrongAlphaRelation:=BoundAbstraction.LUB.galois order)).
    by apply is_alpha_lub_cong.
Qed.

(** * Addition operation. *)

(** γ(r1, m1) + γ(r2, m2) = γ(r1 + r2, gcd(m1, m2)).
    Sum of remainders gives the new remainder; gcd of moduli the new
    modulus — by Bezout, gcd(m1,m2)·Z = m1·Z + m2·Z. *)

Definition cong_add (a2 a1 : Z * Z) : Z * Z :=
  let (r2, m2) := a2 in
  let (r1, m1) := a1 in
  (r2 + r1, Z.gcd m2 m1).

Lemma cong_add_sound:
  binary_overapproximation cong_ad cong_ad cong_ad cong_add
    (collecting_binary_forward Z.add).
Proof.
  overapproximation_proof.
  move: a2 a1 Hc2_in_a2 Hc1_in_a1 => [ra ma] [rb mb] Ha Hb.
  unfold_set in *. move: Hc0 => <-.
  replace (c2 + c1 - (ra + rb)) with ((c2 - ra) + (c1 - rb)) by lia.
  apply Z.divide_add_r.
  - transitivity ma; [apply Z.gcd_divide_l | exact Ha].
  - transitivity mb; [apply Z.gcd_divide_r | exact Hb].
Qed.

(** Underapproximation: every c ∈ γ(r1+r2, gcd m1 m2) decomposes as
    c = c2 + c1 with c2 ∈ γ(r1,m1), c1 ∈ γ(r2,m2). The decomposition
    comes from Bezout's identity: gcd m1 m2 = u·m1 + v·m2. *)
Lemma cong_add_gamma_complete:
  binary_underapproximation cong_ad cong_ad cong_ad cong_add
    (collecting_binary_forward Z.add).
Proof.
  move=> [ra ma] [rb mb] c Hc.
  unfold_set in Hc. move: Hc => [k Hk].
  move: (Zis_gcd_bezout _ _ _ (Zgcd_is_gcd ma mb)) => [u v Huv].
  unfold_set.
  exists (ra + k * u * ma), (rb + k * v * mb). split; [|split].
  - exists (k * u). ring.
  - exists (k * v). ring.
  - nia.
Qed.

Lemma cong_add_exact:
  binary_exact cong_ad cong_ad cong_ad cong_add
    (collecting_binary_forward Z.add).
Proof.
  move=> a2 a1; split; [apply cong_add_gamma_complete|apply cong_add_sound].
Qed.

(** α-completeness of [cong_add]: if [c2] is the best abstraction of
    [S2] and [c1] of [S1], then [cong_add c2 c1] is the best abstraction
    of the collecting sum [S2 + S1]. Unlike intervals, no non-emptiness
    hypothesis on [S2], [S1] is needed: where witnesses are required the
    goal [order ...] is decidable, so we argue by contradiction and
    extract them via [alpha_non_empty] (see the first branch). *)
Lemma cong_add_alpha_complete (c2 c1 : Z * Z) (S2 S1 : ℘ Z) :
  binary_alpha_complete cong_ad cong_ad cong_ad cong_add
    (collecting_binary_forward Z.add) c2 c1 S2 S1.
Proof.
  rewrite /binary_alpha_complete => Ha2 Ha1 a.
  split.
  - (* T ⊆ γ a  ->  cong_add c2 c1 ⊑ a *)
    move: a => [r m] HT.
    (* The goal is [¬¬]-stable, so we may assume concrete witnesses
       s2 ∈ S2, s1 ∈ S1 (extracted via alpha_non_empty_witness). *)
    apply: (alpha_non_empty_witness c2 S2 Ha2) => -[s2 Hs2].
    apply: (alpha_non_empty_witness c1 S1 Ha1) => -[s1 Hs1].
    (* Every x ∈ S2 lands in γ(r - s1, m), via x + s1 ∈ T ⊆ γ(r,m). *)
    have HS2 : S2 ⊆ γ[cong_ad] (r - s1, m).
    { move=> x Hx.
      have Hxs1 : (x + s1) ∈ γ[cong_ad] (r, m) by apply HT; exists x, s1.
      unfold_set in Hxs1. move: Hxs1 => [k Hk]. by exists k; lia. }
    have HS1 : S1 ⊆ γ[cong_ad] (r - s2, m).
    { move=> x Hx.
      have Hs2x : (s2 + x) ∈ γ[cong_ad] (r, m) by apply HT; exists s2, x.
      unfold_set in Hs2x. move: Hs2x => [k Hk]. by exists k; lia. }
    have Hc2 := proj1 (Ha2 (r - s1, m)) HS2.
    have Hc1 := proj1 (Ha1 (r - s2, m)) HS1.
    have Hs2s1 : (s2 + s1) ∈ γ[cong_ad] (r, m) by apply HT; exists s2, s1.
    unfold_set in Hs2s1. move: Hs2s1 => [ks Hks].
    move: c2 c1 Ha2 Ha1 Hc2 Hc1 => [r2 m2] [r1 m1] _ _.
    rewrite /order /cong_add. move=> [Hm2 Hr2] [Hm1 Hr1]. split.
    + by apply Z.gcd_greatest.
    + replace (r2 + r1 - r)
        with ((r2 - (r - s1)) + (r1 - (r - s2)) - (s2 + s1 - r)) by lia.
      apply Z.divide_sub_r; first by apply Z.divide_add_r.
      by exists ks.
  - (* cong_add c2 c1 ⊑ a  ->  T ⊆ γ a *)
    move=> Hle x Hx.
    apply (ad_sqsubseteq_order_preserving cong_ad _ _ Hle).
    apply (cong_add_sound c2 c1).
    unfold_set in Hx. move: Hx => [x2 [x1 [Hx2 [Hx1 Hxeq]]]].
    exists x2, x1.
    split; first exact: proj2 (Ha2 c2) (reflexivity c2) x2 Hx2.
    split; first exact: proj2 (Ha1 c1) (reflexivity c1) x1 Hx1.
    exact Hxeq.
Qed.

(** * Negation. *)

(** -γ(r, m) = γ(-r, m); negation is exact on congruences. *)
Definition cong_opp (a : Z * Z) : Z * Z :=
  let (r, m) := a in (-r, m).

Lemma cong_opp_sound:
  unary_overapproximation cong_ad cong_ad cong_opp (collecting_forward Z.opp).
Proof.
  overapproximation_proof.
  move: a1 Hc1_in_a1 => [r m] Hc.
  unfold_set in *. move: Hc0 => <-.
  move: Hc => [k Hk]. exists (-k). lia.
Qed.

Lemma cong_opp_gamma_complete:
  unary_underapproximation cong_ad cong_ad cong_opp (collecting_forward Z.opp).
Proof.
  move=> [r m] c. unfold_set. move=> [k Hk].
  exists (-c). split; [|lia].
  exists (-k). lia.
Qed.

Lemma cong_opp_exact:
  unary_exact cong_ad cong_ad cong_opp (collecting_forward Z.opp).
Proof.
  move=> a; split; [apply cong_opp_gamma_complete|apply cong_opp_sound].
Qed.

(** * Subtraction. *)

(** Subtraction reduces to addition of the negation. *)
Definition cong_sub (a1 a2 : Z * Z) : Z * Z :=
  cong_add a1 (cong_opp a2).
(* MAYBE: an optimized version. *)

Lemma cong_sub_sound:
  binary_overapproximation cong_ad cong_ad cong_ad cong_sub
    (collecting_binary_forward Z.sub).
Proof.
  overapproximation_proof.
  rewrite /cong_sub. apply cong_add_sound.
  exists c2, (-c1). split; [|split]; [exact Hc2_in_a2 | | lia].
  apply cong_opp_sound. exists c1. split; [exact Hc1_in_a1 | reflexivity].
Qed.

Lemma cong_sub_gamma_complete:
  binary_underapproximation cong_ad cong_ad cong_ad cong_sub
    (collecting_binary_forward Z.sub).
Proof.
  move=> a2 a1 c Hc.
  have /= := cong_add_gamma_complete a2 (cong_opp a1) c Hc.
  unfold_set. move=> [c2 [co [Hc2 [Hco Heq]]]].
  have /= := cong_opp_gamma_complete a1 co Hco.
  unfold_set. move=> [c1 [Hc1 Hco1]].
  exists c2, c1. split; [|split]; [exact Hc2 | exact Hc1 | lia].
Qed.

Lemma cong_sub_exact:
  binary_exact cong_ad cong_ad cong_ad cong_sub
    (collecting_binary_forward Z.sub).
Proof.
  move=> a2 a1; split; [apply cong_sub_gamma_complete|apply cong_sub_sound].
Qed.

(** * Multiplication. *)

(** Granger's rule: (m1·Z + r1) · (m2·Z + r2) ⊆ gcd(r1·m2, r2·m1, m1·m2)·Z + r1·r2.
    Expanding c2·c1 − r1·r2 = r1·(c1−r2) + r2·(c2−r1) + (c2−r1)·(c1−r2)
    shows each summand is divisible by r1·m2, r2·m1, m1·m2 respectively,
    hence by their gcd.

    Note: multiplication is the best (smallest) enclosing congruence but
    is not γ-exact in general. E.g. γ(1,6)·γ(1,10) ⊊ γ(1,2) = odds,
    since 3 ∉ {(6k+1)(10l+1)} (no integer factorization of 3 has that
    form). So we prove soundness only. *)

Definition cong_mul (a1 a2 : Z * Z) : Z * Z :=
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  (r1 * r2, Z.gcd (Z.gcd (r1 * m2) (r2 * m1)) (m1 * m2)).

(** Counterexample to exactness. [cong_mul (1,6) (1,10) = (1,2)], whose
    concretization γ(1,2) is the odd integers; yet 3 — though odd — is
    not a product of an element of γ(1,6) by an element of γ(1,10): that
    would require 3 = (6k+1)·(10l+1), but the only divisors of 3 are
    ±1, ±3, none of which is simultaneously ≡ 1 (mod 6) and ≡ 1 (mod 10).
    So non-exactness is a property of integer multiplication itself, not
    of [cong_mul]: the best enclosing congruence simply cannot be exact. *)
Lemma cong_mul_not_gamma_exact :
  ~ binary_exact cong_ad cong_ad cong_ad cong_mul
      (collecting_binary_forward Z.mul).
Proof.
  move=> Hex.
  have Hc0_in : (3 : Z) ∈ γ[cong_ad] (cong_mul (1, 6) (1, 10)).
  { rewrite /cong_mul. unfold_set. by exists 1. }
  (* Exactness forces 3 into the collecting product set of two odds. *)
  have Hin : (3 : Z) ∈ collecting_binary_forward Z.mul
               (γ[cong_ad] (1, 6)) (γ[cong_ad] (1, 10))
    by case: (Hex (1, 6) (1, 10)) => [Hsub _]; exact: (Hsub 3 Hc0_in).
  clear Hex Hc0_in.
  (* So c2 = 6·k2 + 1, c1 = 10·k1 + 1, with c2·c1 = 3. *)
  move: Hin; unfold_set; move=> -[c2 [c1 [[k2 Hk2] [[k1 Hk1] defc0]]]].
  (* c1 divides 3, so |c1| ≤ 3; enumerate the 7 candidates. *)
  have Hd : (c1 | 3) by exists c2; lia.
  have Hne : (3 : Z) <> 0 by lia.
  have Hb := Zdivide_bounds c1 3 Hd Hne.
  have Hcases : c1 = -3 \/ c1 = -2 \/ c1 = -1 \/ c1 = 0
                \/ c1 = 1 \/ c1 = 2 \/ c1 = 3 by lia.
  by case: Hcases => [Heq|[Heq|[Heq|[Heq|[Heq|[Heq|Heq]]]]]];
     rewrite Heq in defc0 Hk1; lia.
Qed.

Lemma cong_mul_sound:
  binary_overapproximation cong_ad cong_ad cong_ad cong_mul
    (collecting_binary_forward Z.mul).
Proof.
  overapproximation_proof.
  move: a2 a1 Hc2_in_a2 Hc1_in_a1 => [ra ma] [rb mb] Ha Hb.
  unfold_set in *. move: Hc0 => <-.
  move: Ha Hb => [ka Hka] [kb Hkb].
  replace (c2 * c1 - ra * rb)
    with (kb * (ra * mb) + ka * (rb * ma) + (ka * kb) * (ma * mb)) by nia.
  apply Z.divide_add_r; [apply Z.divide_add_r|].
  - apply Z.divide_mul_r. transitivity (Z.gcd (ra * mb) (rb * ma));
      [apply Z.gcd_divide_l | apply Z.gcd_divide_l].
  - apply Z.divide_mul_r. transitivity (Z.gcd (ra * mb) (rb * ma));
      [apply Z.gcd_divide_l | apply Z.gcd_divide_r].
  - apply Z.divide_mul_r. apply Z.gcd_divide_r.
Qed.

(** * Best abstraction for multiplication.

    Granger's rule gives the smallest congruence that overapproximates
    γ(r1,m1)·γ(r2,m2): for any (r', m') that contains this product set,
    (r1·r2, gcd(r1·m2, r2·m1, m1·m2)) ⊑ (r', m'). The proof feeds four
    "corner" products into the hypothesis — (r1,r2), (r1+m1,r2),
    (r1,r2+m2), (r1+m1,r2+m2) — and combines the resulting divisibility
    facts (differences of two, three, four corners) to show m' divides
    each of r1·m2, m1·r2, m1·m2, hence their gcd. *)

Lemma cong_mul_best :
  binary_best cong_ad cong_ad cong_ad cong_mul
    (collecting_binary_forward Z.mul).
Proof.
  move=> [r1 m1] [r2 m2]. split; first by apply: cong_mul_sound.
  move=> [r' m'] HS.
  (* Feeding any (c2, c1) in the two γ's into HS gives m' | c2*c1 - r'. *)
  have in_prod : forall c2 c1,
    c2 ∈ γ[cong_ad] (r1, m1) -> c1 ∈ γ[cong_ad] (r2, m2) ->
    (m' | c2 * c1 - r').
  { move=> c2 c1 H2 H1.
    have Hmem : c2 * c1 ∈ γ[cong_ad] (r', m').
    { apply: HS. unfold_set. by exists c2, c1. }
    by unfold_set in Hmem. }
  (* Four corner points of γ(r1,m1) × γ(r2,m2): *)
  have Hr1     : r1      ∈ γ[cong_ad] (r1, m1) by unfold_set; exists 0; lia.
  have Hr2     : r2      ∈ γ[cong_ad] (r2, m2) by unfold_set; exists 0; lia.
  have Hr1m1   : r1 + m1 ∈ γ[cong_ad] (r1, m1) by unfold_set; exists 1; lia.
  have Hr2m2   : r2 + m2 ∈ γ[cong_ad] (r2, m2) by unfold_set; exists 1; lia.
  have H00 := in_prod _ _ Hr1   Hr2.      (* m' | r1·r2 - r' *)
  have H10 := in_prod _ _ Hr1m1 Hr2.      (* m' | (r1+m1)·r2 - r' *)
  have H01 := in_prod _ _ Hr1   Hr2m2.    (* m' | r1·(r2+m2) - r' *)
  have H11 := in_prod _ _ Hr1m1 Hr2m2.    (* m' | (r1+m1)·(r2+m2) - r' *)
  (* Differences of corners isolate each term. *)
  have Hm1r2 : (m' | m1 * r2).
  { replace (m1 * r2) with ((r1 + m1) * r2 - r' - (r1 * r2 - r')) by ring.
    exact: Z.divide_sub_r H10 H00. }
  have Hr1m2 : (m' | r1 * m2).
  { replace (r1 * m2) with (r1 * (r2 + m2) - r' - (r1 * r2 - r')) by ring.
    exact: Z.divide_sub_r H01 H00. }
  have Hm1m2 : (m' | m1 * m2).
  { replace (m1 * m2)
      with ((r1 + m1) * (r2 + m2) - r' - (r1 * r2 - r') - m1 * r2 - r1 * m2)
      by ring.
    apply: Z.divide_sub_r; [|exact Hr1m2].
    apply: Z.divide_sub_r; [|exact Hm1r2].
    exact: Z.divide_sub_r H11 H00. }
  (* Conclude: (r1·r2, d) ⊑ (r', m') where d is the congruence gcd. *)
  split; last exact: H00.
  apply: Z.gcd_greatest; last exact: Hm1m2.
  apply: Z.gcd_greatest; first exact: Hr1m2.
  by rewrite Z.mul_comm.
Qed.

(** * Division. *)

(** Integer division does not preserve congruence structure in general;
    we identify the cases where a tight result exists:

    - Divide by the singleton {0}: Coq's [a / 0 = 0], so the concrete
      result is {0}, exactly represented by (0, 0).

    - Divide by a nonzero constant r2 with r2 ∣ m1: the concrete set is
      γ(r1/r2, m1/r2) exactly, by Z.div_add.

    - Otherwise: fall back to top (0, 1).

    Note: in the generic "r2 ∣ m1" case we no longer require r2 ∣ r1
    (Coq's [/] is [Z.div], which is defined even on non-multiples).
    Best-abstraction proofs below handle each case separately. *)

(** [cong_div] now returns a [WithBottom]-wrapped result so that the case
    where the divisor abstraction is exactly {0} (no valid divisor under
    the partial semantics) can be represented as [Bot]. *)
Definition cong_div (a1 a2 : Z * Z) : WithBottom.with_bottom (Z * Z) :=
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  if m2 =? 0 then
    if r2 =? 0 then WithBottom.Bot                          (* divisor_zero *)
    else if m1 mod r2 =? 0 then WithBottom.NotBot (r1 / r2, m1 / r2)  (* const_divides *)
    else WithBottom.NotBot (0, 1)                           (* const_pos/neg (top) *)
  else
    if (m1 =? 0) && (r1 =? 0) then WithBottom.NotBot (0, 0) (* dividend_zero *)
    else WithBottom.NotBot (0, 1).                          (* nonconstant_divisor (top) *)

Lemma cong_div_sound:
  binary_overapproximation cong_ad cong_ad (WithBottom.ad cong_ad) cong_div
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div).
Proof.
  move=> a2 a1 c0 [c2 [c1 [Hc2_in_a2 [Hc1_in_a1 [Hc1_ne Hc0]]]]].
  move: a2 a1 Hc2_in_a2 Hc1_in_a1 => [ra ma] [rb mb] Ha Hb.
  rewrite /cong_div.
  have Htop (z : Z) : z ∈ γ[cong_ad] (0, 1).
  { unfold_set. apply Z.divide_1_l. }
  case Hmb: (mb =? 0); last first.
  { (* mb ≠ 0: dividend_zero if dividend is {0}, else top. *)
    move: Hmb => /Z.eqb_neq Hmb.
    case Hr1m1 : ((ma =? 0) && (ra =? 0)); last first.
    - (* nonconstant_divisor (top): NotBot (0, 1), γ = ℤ. *)
      simpl. move: Hc0 => <-. exact: Htop.
    - (* dividend_zero: c2 = 0 forces Z.div 0 c1 = 0 ∈ γ(0,0). *)
      move/andP: Hr1m1 => [/Z.eqb_eq Hma /Z.eqb_eq Hra].
      subst ra ma.
      move/gamma_singleton in Ha.
      simpl. move: Hc0 => <-. rewrite Ha Zdiv_0_l.
      by apply/gamma_singleton. }
  move: Hmb => /Z.eqb_eq Hmb.
  case Hrb: (rb =? 0).
  { (* divisor_zero: divisor set = {0}, but c1 ≠ 0 is required — contradiction. *)
    move: Hrb => /Z.eqb_eq Hrb. subst rb mb.
    move/gamma_singleton in Hb.
    by rewrite Hb in Hc1_ne. }
  move: Hrb => /Z.eqb_neq Hrb.
  case Hma_mod: (ma mod rb =? 0); last first.
  - (* const_pos/neg (top). *)
    simpl. move: Hc0 => <-. exact: Htop.
  - move: Hma_mod => /Z.eqb_eq Hma_mod.
    subst mb. move/gamma_singleton in Hb.
    unfold_set in Ha. move: Ha => [k Hk].
    have Hma_eq : ma = rb * (ma / rb) by have := Z.div_mod ma rb Hrb; lia.
    have Hc2 : c2 = ra + (k * (ma / rb)) * rb by nia.
    simpl. move: Hc0 => <-. rewrite Hc2 Hb (Z.div_add _ _ _ Hrb).
    unfold_set. exists k. lia.
Qed.

(** ** Total-semantics case lemmas (on [cong_ad]).

    Each branch of [cong_div]'s dispatch — keyed by the shape of the
    divisor and dividend — is proved here as a standalone
    [ExactlyRepresents] or [BestAbstraction] over the *total* collecting
    set. The [WithBottom] wrappers further below ([cong_div_best_*]) lift
    these to the partial (divisor ≠ 0) semantics that [cong_div_best]
    dispatches on; the [_total] suffix marks this total-set kernel. *)

(** Divisor is the constant {0}: the result set is {0}, best is (0,0). *)
Lemma cong_div_exact_divisor_zero_total (r1 m1 : Z) :
  ExactlyRepresents (A:=cong_ad) (0, 0)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (0, 0))).
Proof.
  split.
  - (* γ(0,0) ⊆ S *)
    move=> c. move/gamma_singleton => ->. exists r1, 0. split; [|split].
    + by exists 0; lia.
    + by apply/gamma_singleton.
    + exact: Zdiv_0_r.
  - (* S ⊆ γ(0,0) *)
    move=> c. unfold_set. move=> [c2 [c1 [_ [Hc1 Hdef]]]].
    move/gamma_singleton in Hc1.
    rewrite Hc1 Zdiv_0_r in Hdef. subst c.
    by apply/gamma_singleton.
Qed.

Lemma cong_div_best_divisor_zero_total (r1 m1 : Z) :
  BestAbstraction (A:=cong_ad) (0, 0)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (0, 0))).
Proof.
  apply: is_alpha_is_best_abstraction.
  apply: exact_is_is_alpha. exact: cong_div_exact_divisor_zero_total.
Qed.

(** Constant divisor r2 ≠ 0 with r2 ∣ m1: then γ(r1,m1) / {r2} =
    γ(r1/r2, m1/r2) exactly. *)
Lemma cong_div_exact_const_divides_total (r1 m1 r2 : Z) :
  r2 <> 0 -> (r2 | m1) ->
  ExactlyRepresents (A:=cong_ad) (r1 / r2, m1 / r2)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hdivs.
  have Hm1_eq : m1 = (m1 / r2) * r2.
  { case: Hdivs => q ->. by rewrite (Z.div_mul _ _ Hr2). }
  have Hdiv_eq : forall k, (r1 + k * m1) / r2 = r1 / r2 + k * (m1 / r2).
  { move=> k.
    have -> : r1 + k * m1 = r1 + (k * (m1 / r2)) * r2 by nia.
    exact: Z.div_add _ _ _ Hr2. }
  split.
  - (* γ(r1/r2, m1/r2) ⊆ S: given c = r1/r2 + k·(m1/r2), produce
       c2 = r1 + k·m1, c1 = r2 with Z.div c2 r2 = c. *)
    move=> c. unfold_set. move=> [k Hk].
    exists (r1 + k * m1), r2. split; [|split].
    + by exists k; lia.
    + by apply/gamma_singleton.
    + rewrite Hdiv_eq. lia.
  - (* S ⊆ γ(r1/r2, m1/r2): unfold Z.div via Z.div_add. *)
    move=> c. unfold_set.
    move=> [c2 [c1 [[k Hk] [Hc1 Hdef]]]].
    move/gamma_singleton in Hc1. subst c1.
    have Hc2 : c2 = r1 + k * m1 by lia. subst c2.
    by exists k; rewrite -Hdef Hdiv_eq; lia.
Qed.

Lemma cong_div_best_const_divides_total (r1 m1 r2 : Z) :
  r2 <> 0 -> (r2 | m1) ->
  BestAbstraction (A:=cong_ad) (r1 / r2, m1 / r2)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hdivs.
  apply: is_alpha_is_best_abstraction.
  apply: exact_is_is_alpha. exact: cong_div_exact_const_divides_total.
Qed.

(** ** Constant divisor (positive) not dividing m1. Top (0, 1) is the
    best abstraction, but NOT γ-exact: the quotient set
    [{(r1+k·m1)/r2 : k ∈ ℤ}] generally skips integers.

    Proof is constructive (no classical reasoning) so the infrastructure
    ports cleanly to a future Z.quot variant.

    High-level strategy. Let q := m1/r2 and rm := m1 mod r2 (so 0 < rm < r2
    because ¬(r2 ∣ m1)). For any overapproximating abstraction (r', m'), we
    derive m' ∣ 1 — which forces m' = ±1 and hence (0,1) ⊑ (r',m').

    Fix k and look at V(k) := (r1 + k·m1)/r2. Consecutive gaps
    V(k+1) − V(k) equal q + carry(k), where carry(k) ∈ {0, 1}. All gaps
    are divisible by m' (since m' divides each V(k) − r'). So if we can
    exhibit one step with carry = 0 (giving m' ∣ q) and one step with
    carry = 1 (giving m' ∣ q+1), then m' ∣ (q+1) − q = 1.

    Existence of both kinds of step follows from the telescoping sum
    V(r2) − V(0) = m1 = r2·q + rm with 0 < rm < r2: the total carry across
    r2 steps equals rm, which is neither 0 nor r2, so some step carries and
    some doesn't. Helpers [exists_no_carry_step] and [exists_carry_step]
    produce the witnesses constructively via [natlike_ind]. *)

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

(** Main const-positive lemma: top is best when the divisor is a known
    nonzero positive constant and does not divide m1. *)
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

Lemma cong_div_best_const_pos_total r1 m1 r2 :
  0 < r2 -> ~(r2 | m1) ->
  BestAbstraction (A:=cong_ad) (0, 1)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  split.
  - move=> c _. unfold_set. apply: Z.divide_1_l.
  - move=> [r' m'] HS.
    have V_in : forall k, 0 <= k <= r2 -> (m' | (r1 + k*m1) / r2 - r').
    { move=> k _.
      have Hmem : (r1 + k*m1) / r2 ∈ γ[cong_ad] (r', m').
      { apply: HS. unfold_set. exists (r1 + k*m1), r2.
        split; [by exists k; lia
               |split; [by exists 0; lia | reflexivity]]. }
      by unfold_set in Hmem. }
    have Hone := carry_witnesses_divides_one _ _ _ _ _ Hr2 Hnd V_in.
    split; first exact: Hone.
    apply: Z.divide_trans Hone _. exact: Z.divide_1_l.
Qed.

(** Constant negative divisor not dividing m1, by reduction to the positive case.

    Key observation: for c ≠ 0, [Z.div_opp_opp] gives (-a)/(-c) = a/c.
    So for r2 < 0, the quotient set
      {c1/r2 : c1 ∈ γ(r1, m1)}
    equals (via the bijection c1 ↔ -c1)
      {c1'/(-r2) : c1' ∈ γ(-r1, m1)}.
    The latter is exactly the case-C-positive set for (−r1, m1) divided by
    (−r2, 0). We transport [BestAbstraction] across this set equality. *)
Lemma cong_div_best_const_neg_total r1 m1 r2 :
  r2 < 0 -> ~(r2 | m1) ->
  BestAbstraction (A:=cong_ad) (0, 1)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  have Hr2_ne : r2 <> 0 by lia.
  have Hr2' : 0 < -r2 by lia.
  have Hnd' : ~(-r2 | m1).
  { move=> [k Hk]. apply: Hnd. by exists (-k); lia. }
  have HC := cong_div_best_const_pos_total (-r1) m1 (-r2) Hr2' Hnd'.
  have Hset : forall z,
    z ∈ collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))
    <-> z ∈ collecting_binary_forward Z.div (γ[cong_ad] (-r1, m1)) (γ[cong_ad] (-r2, 0)).
  { move=> z. split.
    - move=> H. unfold_set in H. move: H => [c1 [c2 [Hc1 [Hc2 Hd]]]].
      unfold_set. exists (-c1), (-c2). split; [|split].
      + unfold_set in Hc1. unfold_set. case: Hc1 => k Hk. by exists (-k); lia.
      + move/gamma_singleton :Hc2 => ->.
        by exists 0; lia.
      + have Hc2eq : c2 = r2 by move/gamma_singleton :Hc2.
        rewrite Hc2eq. rewrite (Z.div_opp_opp _ _ Hr2_ne).
        by rewrite -Hc2eq.
    - move=> H. unfold_set in H. move: H => [c1' [c2' [Hc1' [Hc2' Hd]]]].
      unfold_set. exists (-c1'), (-c2'). split; [|split].
      + unfold_set in Hc1'. unfold_set. case: Hc1' => k Hk. by exists (-k); lia.
      + move/gamma_singleton :Hc2' => ->.
        by exists 0; lia.
      + have Hc2eq : c2' = -r2 by move/gamma_singleton :Hc2'.
        have Hne : -r2 <> 0 by lia.
        rewrite Hc2eq in Hd. rewrite Hc2eq.
        by rewrite (Z.div_opp_opp _ _ Hne). }
  case: HC => HO HB. split.
  - move=> c Hc. apply: HO. by apply/Hset.
  - move=> [r' m'] Ha'. apply: HB.
    move=> c Hc. apply: Ha'. by apply/Hset.
Qed.

(** ** Non-constant divisor (m2 ≠ 0), split on the dividend.

    Dividend exactly {0} (r1 = m1 = 0): result = {0}, best (0,0).
    Dividend non-{0}: result contains {0, -1}, best (0,1). *)

(** Dividend exactly {0} is actually γ-exact: γ(r1,m1) = {0} forces c1 = 0,
    so every element of S is Z.div 0 c2 = 0, and conversely 0 is reached by
    picking c1 = 0 and any c2 ∈ γ(r2,m2). Thus S = {0} = γ(0,0). *)
Lemma cong_div_exact_dividend_zero_total r2 m2 :
  m2 <> 0 ->
  ExactlyRepresents (A:=cong_ad) (0, 0)
    (collecting_binary_forward Z.div (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  split.
  - (* γ(0,0) ⊆ S: γ(0,0) = {0}, and 0 ∈ S witnessed by c1 = 0, c2 = r2. *)
    move=> c. move/gamma_singleton => ->.
    unfold_set. exists 0, r2. split; [by apply/gamma_singleton|].
    split; [by exists 0; lia|]. by rewrite Zdiv_0_l.
  - (* S ⊆ γ(0,0): any z ∈ S has z = Z.div c1 c2 with c1 ∈ γ(0,0) = {0},
       so c1 = 0 and z = 0/c2 = 0 ∈ γ(0,0). *)
    move=> c Hc. unfold_set in Hc. case: Hc => [c1 [c2 [Ha [_ Hd]]]].
    move/gamma_singleton in Ha.
    rewrite -Hd Ha Zdiv_0_l. by apply/gamma_singleton.
Qed.

Lemma cong_div_best_dividend_zero_total r2 m2 :
  m2 <> 0 ->
  BestAbstraction (A:=cong_ad) (0, 0)
    (collecting_binary_forward Z.div (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  apply: is_alpha_is_best_abstraction.
  apply: exact_is_is_alpha. exact: cong_div_exact_dividend_zero_total.
Qed.

(** Non-constant divisor (m2 ≠ 0) with dividend not exactly {0}. Top (0, 1)
    is best but NOT γ-exact (the quotient set is typically bounded, e.g.
    {r1/c : c ∈ γ(r2,m2)} for m1 = 0 is finite).

    Strategy: force m' ∣ 1 by exhibiting BOTH 0 and −1 in the quotient set.
    Pick any nonzero c1 ∈ γ(r1,m1). Since γ(r2,m2) is an arithmetic
    progression with step |m2| ≥ 1, we can reach divisors of arbitrarily
    large magnitude on both sides: c2p := r2 + A·sgn(m2)·m2 > |c1| and
    c2n := r2 − A·sgn(m2)·m2 < −|c1| (for A := |c1| + |r2| + 1).
    Then c1/c2p and c1/c2n realize {0, −1}:
      - if c1 > 0: c1/c2p = 0 (small nonneg dividend); c1/c2n = −1.
      - if c1 < 0: c1/c2p = −1; c1/c2n = 0 (by symmetric bounds).
    From m' ∣ (0 − r') and m' ∣ (−1 − r'), we get m' ∣ 1. *)
Lemma cong_div_best_nonconstant_divisor_total r1 m1 r2 m2 :
  m2 <> 0 -> (r1 <> 0 \/ m1 <> 0) ->
  BestAbstraction (A:=cong_ad) (0, 1)
    (collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2 Hne.
  split.
  - (* γ(0,1) = ℤ, so S ⊆ γ(0,1) trivially. *)
    move=> c _. unfold_set. exact: Z.divide_1_l.
  - move=> [r' m'] HS.
    (* Step 1: pick c1 ∈ γ(r1,m1) with c1 ≠ 0. *)
    have [c1 [Hc1_in Hc1_ne]] : exists c1, c1 ∈ γ[cong_ad] (r1, m1) /\ c1 <> 0.
    { case: (Z.eq_dec r1 0) => [Hr1|Hr1].
      - (* r1 = 0; then m1 ≠ 0 *)
        have Hm1 : m1 <> 0 by case: Hne => //; rewrite Hr1.
        exists m1. split; last exact Hm1.
        unfold_set. exists 1. lia.
      - exists r1. split; last exact Hr1.
        unfold_set. by exists 0; lia. }
    (* Step 2: construct c2p, c2n ∈ γ(r2,m2) with c2p > |c1|, c2n < -|c1|. *)
    pose A := Z.abs c1 + Z.abs r2 + 1.
    have HA1 : 1 <= A.
    { rewrite /A. have := Z.abs_nonneg c1. have := Z.abs_nonneg r2. lia. }
    have Hm2_abs : 1 <= Z.abs m2.
    { have := Z.abs_nonneg m2.
      case: (Z.abs_spec m2) => [[_ ->]|[_ ->]]; lia. }
    have Hsgn_mul : Z.sgn m2 * m2 = Z.abs m2.
    { have := Z.abs_sgn m2. nia. }
    pose c2p := r2 + A * Z.sgn m2 * m2.
    pose c2n := r2 - A * Z.sgn m2 * m2.
    have Hc2p_eq : c2p = r2 + A * Z.abs m2.
    { rewrite /c2p. have := Hsgn_mul. nia. }
    have Hc2n_eq : c2n = r2 - A * Z.abs m2.
    { rewrite /c2n. have := Hsgn_mul. nia. }
    have Hc1_abs : Z.abs c1 <= c1 \/ c1 <= - Z.abs c1.
    { case: (Z.abs_spec c1); lia. }
    have Hr2_abs : - Z.abs r2 <= r2 <= Z.abs r2.
    { case: (Z.abs_spec r2); lia. }
    have Hc2p_big : Z.abs c1 < c2p.
    { rewrite Hc2p_eq /A. nia. }
    have Hc2n_small : c2n < - Z.abs c1.
    { rewrite Hc2n_eq /A. nia. }
    have Hc2p_pos : 0 < c2p.
    { have := Z.abs_nonneg c1. lia. }
    have Hc2n_neg : c2n < 0.
    { have := Z.abs_nonneg c1. lia. }
    have Hc2p_in : c2p ∈ γ[cong_ad] (r2, m2).
    { unfold_set. exists (A * Z.sgn m2). rewrite /c2p. ring. }
    have Hc2n_in : c2n ∈ γ[cong_ad] (r2, m2).
    { unfold_set. exists (- (A * Z.sgn m2)). rewrite /c2n. ring. }
    (* Step 3: show 0 ∈ S and -1 ∈ S *)
    have Hc1_bounds : - c2p < c1 < c2p.
    { have := Z.abs_nonneg c1. case: (Z.abs_spec c1); lia. }
    have H0_in : 0 ∈ collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)).
    { case: (Z_lt_le_dec 0 c1) => Hsgn.
      - (* c1 > 0: c1/c2p = 0 *)
        unfold_set. exists c1, c2p. split; first done. split; first done.
        apply: Z.div_small. lia.
      - (* c1 < 0: c1/c2n = 0 *)
        unfold_set. exists c1, c2n. split; first done. split; first done.
        have Hc2n_ne : c2n <> 0 by lia.
        apply/Z.div_small_iff => //. right. lia. }
    have Hm1_in : (-1) ∈ collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)).
    { case: (Z_lt_le_dec 0 c1) => Hsgn.
      - (* c1 > 0, c2n < 0 < c1 < -c2n: c1/c2n = -1 *)
        unfold_set. exists c1, c2n. split; first done. split; first done.
        symmetry. apply: (Z.div_unique _ _ (-1) (c1 + c2n)); lia.
      - (* c1 < 0, c2p > -c1 > 0: c1/c2p = -1 *)
        unfold_set. exists c1, c2p. split; first done. split; first done.
        symmetry. apply: (Z.div_unique _ _ (-1) (c1 + c2p)); lia. }
    (* Step 4: both 0 and -1 lie in γ(r',m'), and their difference is 1. *)
    have := HS _ H0_in. unfold_set => H0'.    (* m' | 0 - r' *)
    have := HS _ Hm1_in. unfold_set => Hm1'.  (* m' | -1 - r' *)
    have Hone : (m' | 1).
    { have Hd : (m' | (0 - r') - (-1 - r')) by apply: Z.divide_sub_r.
      have -> : 1 = (0 - r') - (-1 - r') by ring.
      exact Hd. }
    (* order (0, 1) (r', m') = (m' | 1) ∧ (m' | 0 - r'); both established. *)
    split; first exact: Hone.
    exact: H0'.
Qed.

(** ** Lifting helpers to [WithBottom]-wrapped best abstractions.

    The generic lemmas [WithBottom.WithBottom.BestAbstraction_NotBot],
    [WithBottom.BestAbstraction_Bot] (in [AbstractionCombination]) and
    [best_abstraction_equiv] (in [Abstraction]) do the heavy lifting.
    Below we add only a partial/total set-equivalence tailored to
    [collecting_binary_forward(_partial)] when the divisor set has no 0. *)

Lemma collecting_div_partial_total_nz (S2 S1 : propset Z) :
  (forall c, c ∈ S1 -> c <> 0) ->
  collecting_binary_forward Z.div S2 S1 ⊆⊇
  collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div S2 S1.
Proof.
  move=> Hnz. split.
  - move=> c [c2 [c1 [Hc2 [Hc1 Hd]]]].
    exists c2, c1. split; [|split; [|split]]; by [|apply: Hnz].
  - by move=> c [c2 [c1 [Hc2 [Hc1 [_ Hd]]]]]; exists c2, c1.
Qed.

(** ** Best-abstraction case lemmas lifted to [WithBottom]. *)

Lemma cong_div_best_divisor_zero (r1 m1 : Z) :
  BestAbstraction (A:=WithBottom.ad cong_ad) WithBottom.Bot
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (0, 0))).
Proof.
  apply: WithBottom.BestAbstraction_Bot.
  move=> c [c2 [c1 [_ [Hc1 [Hne _]]]]].
  unfold_set in Hc1. case: Hc1 => [k Hk].
  have : c1 = 0 by nia.
  by move/Hne.
Qed.

(** Shared witness that r1/r2 is in the partial set when r2 ≠ 0. *)
Local Lemma const_divisor_elem r1 m1 r2 :
  r2 <> 0 ->
  (r1 / r2) ∈ collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
                (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0)).
Proof.
  move=> Hr2. exists r1, r2.
  split; [by exists 0; lia|].
  split; [by exists 0; lia|].
  split; [exact Hr2 | reflexivity].
Qed.

Lemma cong_div_best_const_divides (r1 m1 r2 : Z) :
  r2 <> 0 -> (r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (r1 / r2, m1 / r2))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hdiv.
  have Hnz : forall c, c ∈ γ[cong_ad] (r2, 0) -> c <> 0.
  { move=> c. move/gamma_singleton => ->. exact: Hr2. }
  have Heq := collecting_div_partial_total_nz _ _ Hnz.
  apply: WithBottom.BestAbstraction_NotBot; first by exists (r1 / r2); exact: const_divisor_elem.
  apply: best_abstraction_equiv; last exact: Heq.
  exact: cong_div_best_const_divides_total.
Qed.

Lemma cong_div_best_const_pos (r1 m1 r2 : Z) :
  0 < r2 -> ~(r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  have Hnz : forall c, c ∈ γ[cong_ad] (r2, 0) -> c <> 0.
  { move=> c. move/gamma_singleton => ->. lia. }
  have Heq := collecting_div_partial_total_nz _ _ Hnz.
  apply: WithBottom.BestAbstraction_NotBot;
    first by exists (r1 / r2); apply: const_divisor_elem; lia.
  apply: best_abstraction_equiv; last exact: Heq.
  exact: cong_div_best_const_pos_total.
Qed.

Lemma cong_div_best_const_neg (r1 m1 r2 : Z) :
  r2 < 0 -> ~(r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  have Hnz : forall c, c ∈ γ[cong_ad] (r2, 0) -> c <> 0.
  { move=> c. move/gamma_singleton => ->. lia. }
  have Heq := collecting_div_partial_total_nz _ _ Hnz.
  apply: WithBottom.BestAbstraction_NotBot;
    first by exists (r1 / r2); apply: const_divisor_elem; lia.
  apply: best_abstraction_equiv; last exact: Heq.
  exact: cong_div_best_const_neg_total.
Qed.

(** Dividend = {0}. The total and partial sets differ when 0 ∈ γ(r2,m2)
    (total has 0 from 0/0, partial has 0 from 0/nonzero). Both are exactly
    {0} under m2 ≠ 0, so the transport is direct. *)
Lemma cong_div_best_dividend_zero (r2 m2 : Z) :
  m2 <> 0 ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 0))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  (* γ(r2, m2) is infinite and has elements ≠ 0. *)
  have [c1 [Hc1_in Hc1_ne]] : exists c1, c1 ∈ γ[cong_ad] (r2, m2) /\ c1 <> 0.
  { case: (Z.eq_dec r2 0) => Hr2.
    - exists (r2 + m2). split; last by rewrite Hr2; lia.
      unfold_set. by exists 1; lia.
    - exists r2. split; last exact Hr2.
      unfold_set. by exists 0; lia. }
  have Heq : collecting_binary_forward Z.div (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))
             ⊆⊇
             collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
               (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2)).
  { split.
    - move=> c [c2 [c1' [Ha [Hb Hd]]]].
      move/gamma_singleton in Ha.
      subst c2. rewrite Zdiv_0_l in Hd. subst c.
      (* c = 0 is still in partial: witness c1 (nonzero). *)
      exists 0, c1. split; [by apply/gamma_singleton|].
      split; [exact Hc1_in|]. split; [exact Hc1_ne|].
      exact: Zdiv_0_l.
    - by move=> c [c2 [c1' [Ha [Hb [_ Hd]]]]]; exists c2, c1'. }
  apply: WithBottom.BestAbstraction_NotBot.
  - exists 0. apply: (proj1 Heq).
    exists 0, c1. split; [by exists 0; lia|].
    split; [exact Hc1_in| exact: Zdiv_0_l].
  - apply: best_abstraction_equiv; last exact: Heq.
    exact: cong_div_best_dividend_zero_total.
Qed.

(** Non-constant divisor. When [0 ∈ γ(r2,m2)] the total and partial
    sets differ only in whether [0] comes from a [c2 = 0] pair. We build
    a partial-set witness of [0] by picking any c1 ∈ γ(r1,m1) and a
    nonzero c2 ∈ γ(r2,m2) of matching sign and larger magnitude; the
    quotient is then forced to [0]. With that, partial ⊆⊇ total. *)
Lemma cong_div_d2_partial_total r1 m1 r2 m2 :
  m2 <> 0 ->
  collecting_binary_forward Z.div (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)) ⊆⊇
  collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
    (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)).
Proof.
  move=> Hm2.
  have Hsgn_mul : Z.sgn m2 * m2 = Z.abs m2 by have := Z.abs_sgn m2; nia.
  have Hm2_abs : 1 <= Z.abs m2.
  { have Hm2' : m2 <> 0 := Hm2.
    case: (Z.abs_spec m2) => [[? ->]|[? ->]]; lia. }
  split; last by move=> c [c2 [c1 [Ha [Hb [_ Hd]]]]]; exists c2, c1.
  move=> c [c2 [c1 [Ha [Hb Hd]]]].
  case: (Z.eq_dec c1 0) => [Hc1_0|Hnz]; last by exists c2, c1.
  subst c1. rewrite Zdiv_0_r in Hd. subst c.
  (* Rebuild 0 via a nonzero c1' of same sign as c2 with |c1'| > |c2|. *)
  pose A := Z.abs c2 + Z.abs r2 + 1.
  pose s := Z.sgn c2 + (if c2 =? 0 then 1 else 0).  (* ensures s ≠ 0 *)
  pose c1' := r2 + (s * A) * Z.sgn m2 * m2.
  have HA : 1 <= A.
  { rewrite /A. have := Z.abs_nonneg c2. have := Z.abs_nonneg r2. lia. }
  have Hs_val : s = 1 \/ s = -1.
  { rewrite /s. case: (Z.eqb_spec c2 0) => [->|Hne] /=.
    - by left.
    - case: (Z.lt_trichotomy c2 0) => [Hl|[Hz|Hp]]; [right|done|left].
      + by rewrite Z.sgn_neg //; lia.
      + by rewrite Z.sgn_pos //; lia. }
  have Hs_sgn : (s = 1 -> 0 <= c2) /\ (s = -1 -> c2 <= 0).
  { rewrite /s. case: (Z.eqb_spec c2 0) => [->|Hne] /=.
    - by split; [|lia].
    - have := Z.sgn_null_iff c2. have := Z.sgn_pos_iff c2.
      have := Z.sgn_neg_iff c2.
      case: (Z.sgn c2); lia. }
  have Hr2_abs : - Z.abs r2 <= r2 <= Z.abs r2 by case: (Z.abs_spec r2); lia.
  have Hc2_abs : - Z.abs c2 <= c2 <= Z.abs c2 by case: (Z.abs_spec c2); lia.
  have Hc1'_eq : c1' = r2 + s * A * Z.abs m2.
  { rewrite /c1'. have := Hsgn_mul. nia. }
  have Hc1'_ne : c1' <> 0 by rewrite Hc1'_eq /A; case: Hs_val => ->; nia.
  have Hc1'_in : c1' ∈ γ[cong_ad] (r2, m2).
  { unfold_set. by exists (s * A * Z.sgn m2); rewrite /c1'; ring. }
  exists c2, c1'. split; first done. split; first done. split; first exact Hc1'_ne.
  apply/Z.div_small_iff => //. rewrite Hc1'_eq /A.
  case: Hs_val => Hs.
  - left. split; [apply (proj1 Hs_sgn); exact Hs | rewrite Hs; nia].
  - right. split; [rewrite Hs; nia | apply (proj2 Hs_sgn); exact Hs].
Qed.

Lemma cong_div_best_nonconstant_divisor (r1 m1 r2 m2 : Z) :
  m2 <> 0 -> (r1 <> 0 \/ m1 <> 0) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2 Hne.
  have Heq := cong_div_d2_partial_total r1 m1 r2 m2 Hm2.
  (* Non-emptiness witness: total contains e.g. r1/r2, hence so does partial. *)
  apply: WithBottom.BestAbstraction_NotBot.
  - exists (r1 / r2). apply: (proj1 Heq).
    exists r1, r2. split; [by exists 0; lia|].
    split; [by exists 0; lia| reflexivity].
  - apply: best_abstraction_equiv; last exact: Heq.
    exact: cong_div_best_nonconstant_divisor_total.
Qed.

(** Aggregate: [cong_div] is a best abstraction for [Z.div] under
    partial semantics (divisor ≠ 0). Dispatches on the [if]-structure. *)
Lemma cong_div_best :
  binary_best cong_ad cong_ad (WithBottom.ad cong_ad) cong_div
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.div).
Proof.
  move=> a2 a1.
  move: a2 a1 => [r1 m1] [r2 m2].
  rewrite /cong_div.
  case Hm2 : (m2 =? 0).
  - move/Z.eqb_eq: Hm2 => ->.
    case Hr2 : (r2 =? 0).
    + move/Z.eqb_eq: Hr2 => ->. exact: cong_div_best_divisor_zero.
    + move/Z.eqb_neq: Hr2 => Hr2.
      case Hdiv : (m1 mod r2 =? 0).
      * move/Z.eqb_eq: Hdiv => Hdiv.
        apply: cong_div_best_const_divides => //.
        by apply/Z.mod_divide.
      * move/Z.eqb_neq: Hdiv => Hdiv.
        have Hnd : ~(r2 | m1).
        { move=> H. apply: Hdiv. by apply/Z.mod_divide. }
        case: (Z_lt_le_dec 0 r2) => Hr2sgn.
        -- exact: cong_div_best_const_pos.
        -- have Hr2lt : r2 < 0 by lia.
           exact: cong_div_best_const_neg.
  - move/Z.eqb_neq: Hm2 => Hm2.
    case Hcond : ((m1 =? 0) && (r1 =? 0)).
    + move/andP: Hcond => [/Z.eqb_eq -> /Z.eqb_eq ->].
      exact: cong_div_best_dividend_zero.
    + apply: cong_div_best_nonconstant_divisor => //.
      case: (Z.eq_dec r1 0) => [Hr1|Hr1]; last by left.
      right. case: (Z.eq_dec m1 0) => [Hm1|//].
      exfalso. move: Hcond. by rewrite Hr1 Hm1.
Qed.

(** * Truncating division [Z.quot].

    [Z.quot] (rounding toward zero, C-style) differs from [Z.div]
    (floor, rounds toward −∞) near zero. For [cong_quot] with a
    constant dividend (m1 = 0) and non-constant divisor (m2 ≠ 0), the
    best abstraction depends on the GCD of quotients [|r1| div |c|] over
    divisor magnitudes [|c| ≤ |r1|] in γ(r2, m2). Computed by walking
    the two magnitude progressions of γ with an early exit at gcd = 1. *)

(** Contribution of a single arithmetic progression [d, d+step, d+2*step, ...]
    of divisor magnitudes (with [1 ≤ d], [1 ≤ step]) to the gcd of
    [ar / d'] over its terms [d' ≤ ar]:

    - if [d > ar]: no term in [[1, ar]], contribute [0] (gcd identity);
    - if [d ≤ ar < d + step]: a single term [d], contribute [ar / d];
    - if [d + step ≤ ar]: at least two terms; the gcd collapses to [1]
      (some term lies in [(ar/2, ar]] with quotient [1]). *)
Definition quot_gcd_progression (ar d step : Z) : Z :=
  if ar <? d then 0
  else if ar <? d + step then ar / d
  else 1.

(* Note: examples of interesting runs:
   10/3+8Z = 10/{-13,-5,3,11}.. = {0,-3,2,0} : gcd = 1.
   10/4+8Z = 10/{-12,-4,4,12}.. = {0,-2,2,0} : gcd = 2.
   10/2+30Z = 10/{-28,2,32}.. = {0,5,0} : gcd = 5. *)

(** GCD of all |r1|-div-|c| for nonzero c ∈ γ(r2, m2) with |c| ≤ |r1|.
    Returns 0 when no such c exists (D2a case). *)
Definition quot_gcd_compute (r1 r2 m2 : Z) : Z :=
  let ar := Z.abs r1 in
  let am := Z.abs m2 in
  let rm := r2 mod am in
  if rm =? 0 then
    quot_gcd_progression ar am am
  else
    (** This could be replaced by a case split:
        - Either one of the quot_gcd_progression is 0 (we take the other);
        - Otherwise, it returns a value in {1;2;3}, and the end result is 2
          only if both are 2. *)
    Z.gcd (quot_gcd_progression ar rm am)
          (quot_gcd_progression ar (am - rm) am).

(** ** Helper lemmas about [quot_gcd_progression]. *)

(** Soundness: [quot_gcd_progression] divides [ar / (d + i·step)] for every
    valid index [i]. *)
Lemma quot_gcd_progression_div ar d step (i : nat) :
  1 <= d -> 1 <= step ->
  d + Z.of_nat i * step <= ar ->
  (quot_gcd_progression ar d step | ar / (d + Z.of_nat i * step)).
Proof.
  move=> Hd Hstep Hbound.
  have Hi_nn : 0 <= Z.of_nat i by lia.
  rewrite /quot_gcd_progression.
  case: (Z.ltb_spec ar d) => Har_d.
  - (* d > ar: contradicts Hbound. *) nia.
  - case: (Z.ltb_spec ar (d + step)) => Har_ds.
    + (* Single-element case: only i = 0 satisfies the bound. *)
      have Hi0 : Z.of_nat i = 0 by nia.
      have -> : d + Z.of_nat i * step = d by nia.
      exact: Z.divide_refl.
    + (* Multi-element case: result is 1, divides anything. *)
      exists (ar / (d + Z.of_nat i * step)). lia.
Qed.

(** Auxiliary: for [1 ≤ x ≤ n < 2·x], [n / x = 1]. *)
Lemma div_eq_one (n x : Z) : 1 <= x -> x <= n < 2 * x -> n / x = 1.
Proof.
  move=> Hx [Hxn Hn2x].
  symmetry. apply: (Z.div_unique_pos n x 1 (n - x)); lia.
Qed.

(** Optimality: any [m'] dividing every [ar / (d + i·step)] (for valid [i])
    divides [quot_gcd_progression ar d step]. *)
Lemma quot_gcd_progression_optimal ar d step (m' : Z) :
  1 <= d -> 1 <= step ->
  (forall i : nat, d + Z.of_nat i * step <= ar ->
     (m' | ar / (d + Z.of_nat i * step))) ->
  (m' | quot_gcd_progression ar d step).
Proof.
  move=> Hd Hstep Hall.
  rewrite /quot_gcd_progression.
  case: (Z.ltb_spec ar d) => Har_d; first exact: Z.divide_0_r.
  case: (Z.ltb_spec ar (d + step)) => Har_ds.
  - (* Single-element case: instantiate Hall at i = 0. *)
    have H0 := Hall 0%nat.
    have Heq : d + Z.of_nat 0 * step = d by simpl; lia.
    rewrite Heq in H0. apply: H0. lia.
  - (* Multi-element case: must show m' | 1. Find an i with quotient 1. *)
    suff: (m' | 1) by case=> q ->; exists q; lia.
    case: (Z_le_dec (2 * step) ar) => Hstep_small.
    + (* 2·step ≤ ar: take i_max = (ar - d) / step. *)
      pose imax := Z.to_nat ((ar - d) / step).
      have Himax_nn : 0 <= (ar - d) / step
        by apply: Z.div_pos; lia.
      have Himax_eq : Z.of_nat imax = (ar - d) / step
        by rewrite /imax Z2Nat.id.
      have Hquot : ar - d = (ar - d) / step * step + (ar - d) mod step
        by have := Z.div_mod (ar - d) step (ltac:(lia) : step <> 0); lia.
      have Hmod_bd : 0 <= (ar - d) mod step < step
        by apply: Z.mod_pos_bound; lia.
      have Hi_le : d + Z.of_nat imax * step <= ar by rewrite Himax_eq; lia.
      have Hi_gt : ar - step < d + Z.of_nat imax * step by rewrite Himax_eq; lia.
      have Hquot_one : ar / (d + Z.of_nat imax * step) = 1.
      { apply: div_eq_one; first lia. lia. }
      have := Hall imax Hi_le. rewrite Hquot_one. by [].
    + (* 2·step > ar: take i = 1. *)
      have H1eq : Z.of_nat 1 = 1 by [].
      have Hi_le : d + Z.of_nat 1 * step <= ar by rewrite H1eq; lia.
      have Hquot_one : ar / (d + Z.of_nat 1 * step) = 1.
      { apply: div_eq_one; first lia. rewrite H1eq. lia. }
      have := Hall 1%nat Hi_le. rewrite Hquot_one. by [].
Qed.

(** ** [quot_gcd_compute] correctness.

    Divisors of γ(r2, m2) with magnitude ≤ |r1| correspond to walks'
    indices. For rm = 0 (γ symmetric), one walk suffices. For rm > 0,
    two walks: positive magnitudes [rm + k·am] and negative magnitudes
    [(am − rm) + k·am]. *)

(** |Z.quot r1 c| = |r1| / |c|. *)
Lemma abs_quot r1 c : c <> 0 ->
  Z.abs (Z.quot r1 c) = Z.abs r1 / Z.abs c.
Proof.
  move=> Hc.
  have Hac : 0 < Z.abs c by case: (Z.abs_spec c); lia.
  rewrite (Z.quot_div _ _ Hc).
  have Hdnn : 0 <= Z.abs r1 / Z.abs c
    by apply: Z.div_pos; [apply: Z.abs_nonneg | exact Hac].
  rewrite !Z.abs_mul (Z.abs_eq _ Hdnn).
  have Hsgn_abs : forall x : Z, x <> 0 -> Z.abs (Z.sgn x) = 1.
  { move=> x Hx. case: (Z_lt_le_dec 0 x) => H.
    - by rewrite Z.sgn_pos.
    - rewrite Z.sgn_neg; lia. }
  case: (Z.eq_dec r1 0) => [->|Hr1].
  - by rewrite Z.sgn_0 Z.abs_0 Z.mul_0_l Z.mul_0_l Zdiv_0_l.
  - rewrite (Hsgn_abs _ Hr1) (Hsgn_abs _ Hc). lia.
Qed.

(** Any c ∈ γ(r, m) nonzero is of the form [c = q*|m| + rm] for some
    q ∈ ℤ, where [rm = r mod |m|] ∈ [0, |m|). *)
Lemma gamma_elem_form c r m :
  m <> 0 -> c ∈ γ[cong_ad] (r, m) ->
  exists q : Z, c = q * Z.abs m + r mod Z.abs m.
Proof.
  move=> Hm Hc.
  unfold_set in Hc. case: Hc => [j Hj].
  set am := Z.abs m.
  have Ham : 0 < am by case: (Z.abs_spec m); lia.
  set rm := r mod am.
  have Hr_eq : r = r / am * am + rm.
  { rewrite /rm. have := Z.div_mod r am (ltac:(lia) : am <> 0). lia. }
  exists (r / am + j * Z.sgn m).
  have Hm_abs := Z.abs_sgn m.
  rewrite /am. rewrite /am in Hr_eq. nia.
Qed.

(** [quot_gcd_compute] divides every [ar / |c|] for c ∈ γ(r2,m2), c ≠ 0,
    |c| ≤ ar (intermediate lemma). *)
Lemma quot_gcd_compute_div_ar_abs r1 r2 m2 c :
  m2 <> 0 -> c ∈ γ[cong_ad] (r2, m2) -> c <> 0 ->
  Z.abs c <= Z.abs r1 ->
  (quot_gcd_compute r1 r2 m2 | Z.abs r1 / Z.abs c).
Proof.
  move=> Hm2 Hc Hnz Hbound.
  set ar := Z.abs r1.
  set am := Z.abs m2.
  set rm := r2 mod am.
  have Ham : 0 < am by case: (Z.abs_spec m2); lia.
  have Hrm_bd : 0 <= rm < am by exact: Z.mod_pos_bound.
  have [q Hq] := gamma_elem_form c r2 m2 Hm2 Hc.
  have Hc_form : c = q * am + rm by rewrite Hq.
  have Hac_pos : 0 < Z.abs c by case: (Z.abs_spec c); lia.
  rewrite /quot_gcd_compute -/ar -/am -/rm.
  case: (Z.eqb_spec rm 0) => Hrm_zero.
  - (* rm = 0: |c| = |q|*am where q ≠ 0 (since c ≠ 0). *)
    have Habs_c : Z.abs c = Z.abs q * am.
    { rewrite Hc_form Hrm_zero Z.add_0_r Z.abs_mul.
      have -> : Z.abs am = am by apply: Z.abs_eq; lia. done. }
    have Hq_nn : 0 < Z.abs q by case: (Z.abs_spec q); lia.
    (* Pick index i such that am + i*am = |q|*am, i.e., i = |q| - 1. *)
    pose i := Z.to_nat (Z.abs q - 1).
    have Hi_eq : am + Z.of_nat i * am = Z.abs c.
    { rewrite Habs_c. rewrite /i Z2Nat.id; lia. }
    have Hi_le : am + Z.of_nat i * am <= ar by rewrite Hi_eq.
    have := quot_gcd_progression_div ar am am i (ltac:(lia) : 1 <= am)
      (ltac:(lia) : 1 <= am) Hi_le.
    rewrite Hi_eq. done.
  - (* rm ≠ 0: c is on pos-side (|c| = rm + k*am) or neg-side (|c| = (am-rm) + k*am). *)
    case: (Z_lt_le_dec 0 c) => Hc_sgn.
    + (* c > 0: c = q*am + rm, q ≥ 0, and c = rm + q*am. *)
      have Habs_c : Z.abs c = rm + q * am.
      { rewrite Hc_form. case: (Z.abs_spec c); lia. }
      have Hq_nn : 0 <= q by nia.
      pose i := Z.to_nat q.
      have Hi_eq : rm + Z.of_nat i * am = Z.abs c
        by rewrite Habs_c /i Z2Nat.id; lia.
      have Hi_le : rm + Z.of_nat i * am <= ar by rewrite Hi_eq.
      have Hpos := quot_gcd_progression_div ar rm am i
        (ltac:(lia) : 1 <= rm) (ltac:(lia) : 1 <= am) Hi_le.
      rewrite Hi_eq in Hpos.
      apply: Z.divide_trans; first exact: Z.gcd_divide_l. exact: Hpos.
    + (* c < 0: |c| = q' * am + (am - rm) for q' = -q - 1 ≥ 0. *)
      have Hc_lt : c < 0 by lia.
      have Hq_neg : q <= -1.
      { case: (Z_lt_le_dec q 0); last by nia. lia. }
      pose q' := -q - 1.
      have Hq'_nn : 0 <= q' by rewrite /q'; lia.
      have Habs_c : Z.abs c = (am - rm) + q' * am.
      { rewrite Hc_form. case: (Z.abs_spec c); nia. }
      pose i := Z.to_nat q'.
      have Hi_eq : (am - rm) + Z.of_nat i * am = Z.abs c
        by rewrite Habs_c /i Z2Nat.id; lia.
      have Hi_le : (am - rm) + Z.of_nat i * am <= ar by rewrite Hi_eq.
      have Hneg := quot_gcd_progression_div ar (am - rm) am i
        (ltac:(lia) : 1 <= am - rm) (ltac:(lia) : 1 <= am) Hi_le.
      rewrite Hi_eq in Hneg.
      apply: Z.divide_trans; first exact: Z.gcd_divide_r. exact: Hneg.
Qed.

(** Sound direction: [quot_gcd_compute] divides every [Z.quot r1 c]. *)
Lemma quot_gcd_compute_divides r1 r2 m2 c :
  m2 <> 0 -> c ∈ γ[cong_ad] (r2, m2) -> c <> 0 ->
  (quot_gcd_compute r1 r2 m2 | Z.quot r1 c).
Proof.
  move=> Hm2 Hc Hnz.
  apply/Z.divide_abs_r. rewrite abs_quot //.
  case: (Z_lt_le_dec (Z.abs r1) (Z.abs c)) => Hbound.
  - (* |c| > |r1|: ar / |c| = 0. *)
    have Hac_pos : 0 < Z.abs c by case: (Z.abs_spec c); lia.
    have -> : Z.abs r1 / Z.abs c = 0
      by apply: Z.div_small; split; [apply: Z.abs_nonneg | exact Hbound].
    exact: Z.divide_0_r.
  - exact: quot_gcd_compute_div_ar_abs.
Qed.

(** Optimality: any m' that divides every [Z.quot r1 c] divides
    [quot_gcd_compute r1 r2 m2]. *)
Lemma quot_gcd_compute_optimal r1 r2 m2 (m' : Z) :
  m2 <> 0 ->
  (forall c, c ∈ γ[cong_ad] (r2, m2) -> c <> 0 -> (m' | Z.quot r1 c)) ->
  (m' | quot_gcd_compute r1 r2 m2).
Proof.
  move=> Hm2 Hall.
  set ar := Z.abs r1.
  set am := Z.abs m2.
  set rm := r2 mod am.
  have Ham : 0 < am by case: (Z.abs_spec m2); lia.
  have Hrm_bd : 0 <= rm < am by exact: Z.mod_pos_bound.
  have Hsgn_mul : Z.sgn m2 * m2 = Z.abs m2 by have := Z.abs_sgn m2; nia.
  (* Convert: m' divides ar/|c| for each valid |c|. *)
  have Hdiv_abs : forall c, c ∈ γ[cong_ad] (r2, m2) -> c <> 0 ->
    (m' | Z.abs r1 / Z.abs c).
  { move=> c Hc Hnz. rewrite -abs_quot //. apply/Z.divide_abs_r. exact: Hall. }
  rewrite /quot_gcd_compute -/ar -/am -/rm.
  case: (Z.eqb_spec rm 0) => Hrm_zero.
  - (* rm = 0: elements of γ are (i+1)*am for i ≥ 0. *)
    apply: quot_gcd_progression_optimal; [lia | lia |].
    move=> i Hd.
    set d := am + Z.of_nat i * am.
    pose c := d.
    have Hr2_eq : r2 = r2 / am * am.
    { have := Z.div_mod r2 am (ltac:(lia) : am <> 0).
      fold rm. rewrite Hrm_zero. lia. }
    have Hc_in : c ∈ γ[cong_ad] (r2, m2).
    { unfold_set. rewrite /c /d.
      exists ((Z.of_nat i + 1 - r2 / am) * Z.sgn m2).
      have := Hsgn_mul. nia. }
    have Hc_ne : c <> 0.
    { rewrite /c /d. have := Z.of_nat i. nia. }
    have Habs : Z.abs c = d by rewrite /c /d; apply: Z.abs_eq; nia.
    have := Hdiv_abs c Hc_in Hc_ne. rewrite Habs. done.
  - (* rm ≠ 0: combine two progressions via Z.gcd_greatest. *)
    have Hr2_eq : r2 = r2 / am * am + rm.
    { have := Z.div_mod r2 am (ltac:(lia) : am <> 0). lia. }
    apply: Z.gcd_greatest.
    + (* Positive side: |c| = rm + i·am for c = rm + i·am > 0. *)
      apply: quot_gcd_progression_optimal; [lia | lia |].
      move=> i Hd. set d := rm + Z.of_nat i * am.
      pose c := d.
      have Hc_in : c ∈ γ[cong_ad] (r2, m2).
      { unfold_set. rewrite /c /d.
        exists ((Z.of_nat i - r2 / am) * Z.sgn m2).
        have := Hsgn_mul. nia. }
      have Hc_ne : c <> 0 by rewrite /c /d; nia.
      have Habs : Z.abs c = d by rewrite /c /d; apply: Z.abs_eq; nia.
      have := Hdiv_abs c Hc_in Hc_ne. rewrite Habs. done.
    + (* Negative side: |c| = (am - rm) + i·am for c = -(d) < 0. *)
      apply: quot_gcd_progression_optimal; [lia | lia |].
      move=> i Hd. set d := (am - rm) + Z.of_nat i * am.
      pose c := -d.
      have Hc_in : c ∈ γ[cong_ad] (r2, m2).
      { unfold_set. rewrite /c /d.
        exists ((-(Z.of_nat i + 1) - r2 / am) * Z.sgn m2).
        have := Hsgn_mul. nia. }
      have Hc_ne : c <> 0 by rewrite /c /d; nia.
      have Habs : Z.abs c = d.
      { rewrite /c Z.abs_opp. rewrite /d. apply: Z.abs_eq. nia. }
      have := Hdiv_abs c Hc_in Hc_ne. rewrite Habs. done.
Qed.

Definition cong_quot (a1 a2 : Z * Z) : WithBottom.with_bottom (Z * Z) :=
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  if m2 =? 0 then
    if r2 =? 0 then WithBottom.Bot                                   (* divisor_zero *)
    else if (m1 =? 0) || ((m1 mod r2 =? 0) && (r1 mod r2 =? 0)) then
           WithBottom.NotBot (Z.quot r1 r2, Z.quot m1 r2)            (* const_divides *)
    else WithBottom.NotBot (0, 1)                                    (* top (const_pos/neg) *)
  else
    if m1 =? 0 then
      WithBottom.NotBot (0, quot_gcd_compute r1 r2 m2)               (* D2a / gcd case *)
    else WithBottom.NotBot (0, 1).                                   (* top (m1 ≠ 0) *)

(** Identity used by [const_divides]: when [r2 ∣ m1] and ([m1 = 0] ∨ [r2 ∣ r1]),
    every dividend [r1 + k·m1] is a multiple of [r2], so [Z.quot] is exact. *)
Lemma cong_quot_const_divides_eq r1 m1 r2 k :
  r2 <> 0 ->
  (m1 = 0 \/ ((r2 | m1) /\ (r2 | r1))) ->
  Z.quot (r1 + k * m1) r2 = Z.quot r1 r2 + k * Z.quot m1 r2.
Proof.
  move=> Hr2 [Hm1 | [[qm Hqm] [qr Hqr]]].
  - subst m1. rewrite (Z.quot_0_l _ Hr2).
    have -> : r1 + k * 0 = r1 by ring.
    by rewrite Z.mul_0_r Z.add_0_r.
  - (* r1 = qr*r2, m1 = qm*r2 ⇒ r1 + k*m1 = (qr + k*qm)*r2 *)
    subst r1 m1.
    rewrite (Z.quot_mul _ _ Hr2) (Z.quot_mul _ _ Hr2).
    have -> : qr * r2 + k * (qm * r2) = (qr + k * qm) * r2 by ring.
    by rewrite (Z.quot_mul _ _ Hr2).
Qed.

Lemma cong_quot_sound:
  binary_overapproximation cong_ad cong_ad (WithBottom.ad cong_ad) cong_quot
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot).
Proof.
  move=> a2 a1 c0 [c2 [c1 [Hc2_in_a2 [Hc1_in_a1 [Hc1_ne Hc0]]]]].
  move: a2 a1 Hc2_in_a2 Hc1_in_a1 => [ra ma] [rb mb] Ha Hb.
  rewrite /cong_quot.
  have Htop (z : Z) : z ∈ γ[cong_ad] (0, 1).
  { unfold_set. apply Z.divide_1_l. }
  case Hmb: (mb =? 0); last first.
  { move: Hmb => /Z.eqb_neq Hmb.
    case Hma : (ma =? 0); last first.
    - simpl. move: Hc0 => <-. exact: Htop.
    - move/Z.eqb_eq: Hma => Hma.
      unfold_set in Ha. case: Ha => [k Hk].
      have Hc2 : c2 = ra by nia.
      simpl. move: Hc0 => <-. rewrite Hc2.
      unfold_set.
      have [j Hj] : (quot_gcd_compute ra rb mb | Z.quot ra c1)
        by apply: quot_gcd_compute_divides.
      by exists j; lia. }
  move: Hmb => /Z.eqb_eq Hmb.
  case Hrb: (rb =? 0).
  { move: Hrb => /Z.eqb_eq Hrb. subst rb mb.
    move/gamma_singleton in Hb.
    by rewrite Hb in Hc1_ne. }
  move: Hrb => /Z.eqb_neq Hrb.
  case Hcond : ((ma =? 0) || ((ma mod rb =? 0) && (ra mod rb =? 0))); last first.
  - simpl. move: Hc0 => <-. exact: Htop.
  - unfold_set in Ha. unfold_set in Hb. case: Ha => [k Hk]. case: Hb => [k' Hk'].
    have Hc1_eq : c1 = rb by nia.
    have Hc2 : c2 = ra + k * ma by nia.
    have Hdivs : ma = 0 \/ ((rb | ma) /\ (rb | ra)).
    { move: Hcond => /orP [/Z.eqb_eq ->|/andP [/Z.eqb_eq Hmam /Z.eqb_eq Hram]];
        [by left | right].
      split; by apply/Z.mod_divide. }
    simpl. move: Hc0 => <-. rewrite Hc2 Hc1_eq.
    rewrite (cong_quot_const_divides_eq _ _ _ _ Hrb Hdivs).
    unfold_set. by exists k; lia.
Qed.

(** ** Best-abstraction case lemmas for [cong_quot]. *)

Lemma cong_quot_best_divisor_zero (r1 m1 : Z) :
  BestAbstraction (A:=WithBottom.ad cong_ad) WithBottom.Bot
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (0, 0))).
Proof.
  apply: WithBottom.BestAbstraction_Bot.
  move=> c [c2 [c1 [_ [Hc1 [Hne _]]]]].
  unfold_set in Hc1. case: Hc1 => [k Hk].
  have : c1 = 0 by nia.
  by move/Hne.
Qed.

(** D1 analogue for quot: dividend = {0} forces every quotient to be 0. *)
Lemma cong_quot_exact_dividend_zero r2 m2 :
  m2 <> 0 ->
  ExactlyRepresents (A:=cong_ad) (0, 0)
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  (* Witness a nonzero element of γ(r2, m2). *)
  have [c1 [Hc1_in Hc1_ne]] : exists c, c ∈ γ[cong_ad] (r2, m2) /\ c <> 0.
  { case: (Z.eq_dec r2 0) => Hr2.
    - exists (r2 + m2). split; last by rewrite Hr2; lia.
      unfold_set. by exists 1; lia.
    - exists r2. split; last exact Hr2.
      unfold_set. by exists 0; lia. }
  split.
  - (* γ(0,0) ⊆ S: γ(0,0) = {0}; 0 ∈ S via (c2 := 0, c1 := c1, c1 ≠ 0). *)
    move=> c. move/gamma_singleton => ->.
    exists 0, c1. split; [by apply/gamma_singleton|].
    split; [exact Hc1_in|]. split; [exact Hc1_ne|].
    by rewrite (Z.quot_0_l _ Hc1_ne).
  - (* S ⊆ γ(0,0): every element is 0. *)
    move=> c [c2 [c1' [Ha [_ [Hne Hd]]]]].
    move/gamma_singleton in Ha.
    rewrite Ha (Z.quot_0_l _ Hne) in Hd. subst c.
    by apply/gamma_singleton.
Qed.

Lemma cong_quot_best_dividend_zero r2 m2 :
  m2 <> 0 ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 0))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (0, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  have [c1 [Hc1_in Hc1_ne]] : exists c, c ∈ γ[cong_ad] (r2, m2) /\ c <> 0.
  { case: (Z.eq_dec r2 0) => Hr2.
    - exists (r2 + m2). split; last by rewrite Hr2; lia.
      unfold_set. by exists 1; lia.
    - exists r2. split; last exact Hr2.
      unfold_set. by exists 0; lia. }
  apply: WithBottom.BestAbstraction_NotBot.
  - (* non-empty S witness *)
    exists 0, 0, c1. split; [by exists 0; lia|].
    split; [exact Hc1_in|]. split; [exact Hc1_ne|].
    exact: Z.quot_0_l.
  - apply: is_alpha_is_best_abstraction.
    apply: exact_is_is_alpha. exact: cong_quot_exact_dividend_zero.
Qed.

(** const_divides exact case: [r2 | m1 ∧ (m1 = 0 ∨ r2 | r1)]. *)
Lemma cong_quot_exact_const_divides r1 m1 r2 :
  r2 <> 0 ->
  (m1 = 0 \/ ((r2 | m1) /\ (r2 | r1))) ->
  ExactlyRepresents (A:=cong_ad) (Z.quot r1 r2, Z.quot m1 r2)
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hdivs.
  split.
  - (* γ(Z.quot r1 r2, Z.quot m1 r2) ⊆ S *)
    move=> c Hc. unfold_set in Hc. case: Hc => [k Hk].
    exists (r1 + k * m1), r2.
    split; [by exists k; lia|].
    split; [by exists 0; lia|]. split; first exact Hr2.
    rewrite (cong_quot_const_divides_eq _ _ _ _ Hr2 Hdivs). lia.
  - (* S ⊆ γ *)
    move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]].
    unfold_set in Ha. move/gamma_singleton in Hb.
    case: Ha => [k Hk].
    have Hc2_eq : c2 = r1 + k * m1 by lia.
    subst c. rewrite Hc2_eq Hb.
    rewrite (cong_quot_const_divides_eq _ _ _ _ Hr2 Hdivs).
    unfold_set. by exists k; lia.
Qed.

Lemma cong_quot_best_const_divides r1 m1 r2 :
  r2 <> 0 ->
  (m1 = 0 \/ ((r2 | m1) /\ (r2 | r1))) ->
  BestAbstraction (A:=WithBottom.ad cong_ad)
    (WithBottom.NotBot (Z.quot r1 r2, Z.quot m1 r2))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hdivs.
  apply: WithBottom.BestAbstraction_NotBot.
  - (* witness: Z.quot r1 r2 ∈ S via (c2 := r1, c1 := r2 ≠ 0) *)
    exists (Z.quot r1 r2), r1, r2. split; [by exists 0; lia|].
    split; [by exists 0; lia|]. split; [exact Hr2 | reflexivity].
  - apply: is_alpha_is_best_abstraction.
    apply: exact_is_is_alpha. exact: cong_quot_exact_const_divides.
Qed.

(** [const_pos_nondivides] for quot, [m1 > 0] only.

    The carry argument [carry_witnesses_divides_one] wants witnesses
    for [k ∈ [0, r2]] with [Z.div] computations. Z.quot agrees with
    Z.div on nonneg dividends, so we shift the witness range by
    [K := |r1|]: with [m1 ≥ 1], [r1 + K·m1 ≥ 0] regardless of r1's
    sign, and the shifted base [r1' := r1 + K·m1] satisfies the nonneg
    condition. Since [γ(r1', m1) = γ(r1, m1)] (same congruence class),
    the witnesses come from the original set. *)
Lemma cong_quot_best_const_pos_m1_pos r1 m1 r2 :
  0 < r2 -> 0 < m1 -> ~(r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hm1 Hnd.
  have Hr2_ne : r2 <> 0 by lia.
  apply: WithBottom.BestAbstraction_NotBot.
  - (* non-emptiness: Z.quot r1 r2 ∈ S *)
    exists (Z.quot r1 r2), r1, r2. split; [by exists 0; lia|].
    split; [by exists 0; lia|]. split; [exact Hr2_ne | reflexivity].
  - split.
    + move=> c _. unfold_set. exact: Z.divide_1_l.
    + move=> [r' m'] HS.
      pose K := Z.abs r1.
      pose r1' := r1 + K * m1.
      have Habs : - Z.abs r1 <= r1 by case: (Z.abs_spec r1); lia.
      have Hr1'_nn : 0 <= r1'.
      { rewrite /r1' /K. nia. }
      (* V_in with shifted base: every k ∈ [0, r2] gives nonneg dividend. *)
      have V_in : forall k, 0 <= k <= r2 -> (m' | (r1' + k*m1) / r2 - r').
      { move=> k Hk.
        have Hnonneg : 0 <= r1' + k*m1 by rewrite /r1' /K; nia.
        have Hmem : Z.quot (r1' + k*m1) r2 ∈ γ[cong_ad] (r', m').
        { apply: HS. exists (r1' + k*m1), r2.
          split.
          - (* r1' + k*m1 = r1 + (K+k)*m1 ∈ γ(r1, m1) *)
            exists (K + k). rewrite /r1'. lia.
          - split; [by exists 0; lia|].
            split; [exact Hr2_ne | reflexivity]. }
        unfold_set in Hmem.
        by rewrite (Z.quot_div_nonneg _ _ Hnonneg Hr2) in Hmem. }
      have Hone := carry_witnesses_divides_one _ _ _ _ _ Hr2 Hnd V_in.
      split; first exact: Hone.
      apply: Z.divide_trans Hone _. exact: Z.divide_1_l.
Qed.

(** γ(r, m) = γ(r, -m): the congruence class is sign-insensitive in the step. *)
Local Lemma cong_gamma_sym_m r m :
  γ[cong_ad] (r, m) ⊆⊇ γ[cong_ad] (r, -m).
Proof.
  split; move=> c; unfold_set => [[k Hk]]; unfold_set;
    exists (-k); lia.
Qed.

(** Transport of [collecting_binary_forward_partial] along γ-equivalence
    in the dividend set, for any fixed divisor set. *)
Local Lemma collecting_quot_gamma_cong_l r1 m1 m1' (S1 : propset Z) :
  γ[cong_ad] (r1, m1) ⊆⊇ γ[cong_ad] (r1, m1') ->
  collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
    (γ[cong_ad] (r1, m1)) S1
  ⊆⊇
  collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
    (γ[cong_ad] (r1, m1')) S1.
Proof.
  move=> [Hsub1 Hsub2]. split.
  - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]]. exists c2, c1.
    split; [exact: Hsub1 | split; done].
  - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]]. exists c2, c1.
    split; [exact: Hsub2 | split; done].
Qed.

(** Full positive-divisor case: any m1 ≠ 0. Reduces [m1 < 0] to [m1 > 0]
    via γ(r1, m1) = γ(r1, -m1). *)
Lemma cong_quot_best_const_pos r1 m1 r2 :
  0 < r2 -> ~(r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  have Hm1_ne : m1 <> 0.
  { move=> H. apply: Hnd. by exists 0; lia. }
  case: (Z_lt_le_dec 0 m1) => Hm1_sgn.
  - exact: cong_quot_best_const_pos_m1_pos.
  - have Hmm1 : 0 < -m1 by lia.
    have Hnd' : ~(r2 | -m1).
    { move=> [k Hk]. apply: Hnd. by exists (-k); lia. }
    apply: best_abstraction_equiv;
      last (symmetry; apply: collecting_quot_gamma_cong_l; exact: cong_gamma_sym_m).
    exact: cong_quot_best_const_pos_m1_pos _ _ _ Hr2 Hmm1 Hnd'.
Qed.

(** Sign-correction: for [c < 0] with [r ∤ c], [Z.quot c r = Z.div c r + 1].
    (For [c ≥ 0] or [r ∣ c], Z.quot and Z.div agree.) *)
Lemma Z_quot_neg_nondivides c r :
  0 < r -> c < 0 -> ~(r | c) ->
  Z.quot c r = Z.div c r + 1.
Proof.
  move=> Hr Hc Hnd.
  have Hr_ne : r <> 0 by lia.
  have Hmod_nc : (-c) mod r <> 0.
  { move=> Heq. apply: Hnd.
    have [k Hk] : (r | -c) by apply/Z.mod_divide.
    by exists (-k); lia. }
  have Hnc_nn : 0 <= -c by lia.
  have Hqc : Z.quot c r = -(Z.div (-c) r).
  { have Hc_eq : c = -(-c) by ring.
    rewrite {1}Hc_eq (Z.quot_opp_l _ _ Hr_ne).
    by rewrite (Z.quot_div_nonneg _ _ Hnc_nn Hr). }
  have Hdc : Z.div c r = -(Z.div (-c) r) - 1.
  { have := Z.div_opp_l_nz (-c) r Hr_ne Hmod_nc.
    by rewrite Z.opp_involutive => ->. }
  lia.
Qed.

(** [const_divides_ndr1] sub-case: [r2 > 0 ∧ m1 > 0 ∧ r2 ∣ m1 ∧ r2 ∤ r1].
    The quot set contains both a "regular" gap of q (between two
    positive-dividend witnesses) and a reduced gap of q − 1 (at the
    sign-transition between c1 ≥ 0 and c1 < 0). Hence m' ∣ q and
    m' ∣ q − 1, forcing m' ∣ 1. *)
Lemma cong_quot_best_const_divides_ndr1_m1_pos r1 m1 r2 :
  0 < r2 -> 0 < m1 -> (r2 | m1) -> ~(r2 | r1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hm1 Hr2_divs_m1 Hnd.
  have Hr2_ne : r2 <> 0 by lia.
  have Hm1_ne : m1 <> 0 by lia.
  case: Hr2_divs_m1 => q_ Hq_eq.
  have Hq_pos : 0 < q_ by nia.
  apply: WithBottom.BestAbstraction_NotBot.
  - exists (Z.quot r1 r2), r1, r2. split; [by exists 0; lia|].
    split; [by exists 0; lia|]. split; [exact Hr2_ne | reflexivity].
  - split.
    + move=> c _. unfold_set. exact: Z.divide_1_l.
    + move=> [r' m'] HS.
      (* Choose k_a such that c1_a := r1 + k_a*m1 ∈ [0, m1). *)
      pose k_a := -(r1 / m1).
      pose c1_a := r1 + k_a * m1.
      pose c1_b := c1_a - m1.    (* in [-m1, 0), same residue mod m1, so same mod r2 *)
      pose c1_c := c1_a + m1.    (* in [m1, 2m1), nonneg *)
      have Hc1a_range : 0 <= c1_a < m1.
      { rewrite /c1_a /k_a.
        have := Z.mod_pos_bound r1 m1 Hm1.
        have := Z.div_mod r1 m1 Hm1_ne. lia. }
      have Hc1b_range : -m1 <= c1_b < 0 by rewrite /c1_b; lia.
      have Hc1c_range : m1 <= c1_c < 2*m1 by rewrite /c1_c; lia.
      (* Membership in γ(r1, m1) *)
      have Ha_in : c1_a ∈ γ[cong_ad] (r1, m1) by unfold_set; exists k_a; lia.
      have Hb_in : c1_b ∈ γ[cong_ad] (r1, m1).
      { unfold_set. exists (k_a - 1). rewrite /c1_b /c1_a. lia. }
      have Hc_in : c1_c ∈ γ[cong_ad] (r1, m1).
      { unfold_set. exists (k_a + 1). rewrite /c1_c /c1_a. lia. }
      (* r2 ∤ c1_b (same residue mod r2 as r1, which r2 ∤) *)
      have Hb_nd : ~(r2 | c1_b).
      { move=> [l Hl]. apply: Hnd.
        have Hc1b_expr : c1_b = r1 + (k_a - 1) * (q_ * r2)
          by rewrite /c1_b /c1_a; rewrite -Hq_eq; ring.
        exists (l - (k_a - 1) * q_). nia. }
      (* Z.quot values *)
      have Hqa_div : Z.quot c1_a r2 = Z.div c1_a r2
        by apply: Z.quot_div_nonneg; lia.
      have Hqc_div : Z.quot c1_c r2 = Z.div c1_c r2
        by apply: Z.quot_div_nonneg; lia.
      have Hqb_div : Z.quot c1_b r2 = Z.div c1_b r2 + 1.
      { apply: Z_quot_neg_nondivides => //; lia. }
      (* Z.div values: linear via Z.div_add *)
      have Hdiv_add : forall (c : Z) (k : Z),
          c = c1_a + k * m1 -> Z.div c r2 = Z.div c1_a r2 + k * q_.
      { move=> c k ->.
        have -> : c1_a + k * m1 = c1_a + (k * q_) * r2 by nia.
        by rewrite (Z.div_add _ _ _ Hr2_ne). }
      have Hda_b : Z.div c1_b r2 = Z.div c1_a r2 - q_.
      { have : Z.div c1_b r2 = Z.div c1_a r2 + (-1) * q_.
        { apply: Hdiv_add. rewrite /c1_b. ring. }
        lia. }
      have Hda_c : Z.div c1_c r2 = Z.div c1_a r2 + q_.
      { have : Z.div c1_c r2 = Z.div c1_a r2 + 1 * q_.
        { apply: Hdiv_add. rewrite /c1_c. ring. }
        lia. }
      (* Feed HS *)
      have Hma_in : Z.quot c1_a r2 ∈ γ[cong_ad] (r', m').
      { apply: HS. exists c1_a, r2. split; [exact Ha_in|].
        split; [by exists 0; lia|]. split; [exact Hr2_ne | reflexivity]. }
      have Hmb_in : Z.quot c1_b r2 ∈ γ[cong_ad] (r', m').
      { apply: HS. exists c1_b, r2. split; [exact Hb_in|].
        split; [by exists 0; lia|]. split; [exact Hr2_ne | reflexivity]. }
      have Hmc_in : Z.quot c1_c r2 ∈ γ[cong_ad] (r', m').
      { apply: HS. exists c1_c, r2. split; [exact Hc_in|].
        split; [by exists 0; lia|]. split; [exact Hr2_ne | reflexivity]. }
      unfold_set in Hma_in. unfold_set in Hmb_in. unfold_set in Hmc_in.
      set x := Z.div c1_a r2.
      (* m' | (Z.quot c1_a - r') - (Z.quot c1_b - r') = Z.quot c1_a - Z.quot c1_b *)
      have Hqab : (m' | q_ - 1).
      { have H := Z.divide_sub_r _ _ _ Hma_in Hmb_in.
        have Heq : (Z.quot c1_a r2 - r') - (Z.quot c1_b r2 - r') = q_ - 1.
        { rewrite Hqa_div Hqb_div Hda_b /x. lia. }
        by rewrite Heq in H. }
      have Hqca : (m' | q_).
      { have H := Z.divide_sub_r _ _ _ Hmc_in Hma_in.
        have Heq : (Z.quot c1_c r2 - r') - (Z.quot c1_a r2 - r') = q_.
        { rewrite Hqa_div Hqc_div Hda_c /x. lia. }
        by rewrite Heq in H. }
      have Hone : (m' | 1).
      { have H := Z.divide_sub_r _ _ _ Hqca Hqab.
        by have -> : 1 = q_ - (q_ - 1) by lia. }
      split; first exact: Hone.
      apply: Z.divide_trans Hone _. exact: Z.divide_1_l.
Qed.

(** Any sign of [m1], for [0 < r2] and [r2 ∣ m1, r2 ∤ r1]. *)
Lemma cong_quot_best_const_divides_ndr1_pos r1 m1 r2 :
  0 < r2 -> m1 <> 0 -> (r2 | m1) -> ~(r2 | r1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hm1 Hdiv Hnd.
  case: (Z_lt_le_dec 0 m1) => Hm1_sgn.
  - exact: cong_quot_best_const_divides_ndr1_m1_pos.
  - have Hmm1 : 0 < -m1 by lia.
    have Hdiv' : (r2 | -m1) by case: Hdiv => [q ->]; exists (-q); lia.
    apply: best_abstraction_equiv;
      last (symmetry; apply: collecting_quot_gamma_cong_l; exact: cong_gamma_sym_m).
    exact: cong_quot_best_const_divides_ndr1_m1_pos _ _ _ Hr2 Hmm1 Hdiv' Hnd.
Qed.

(** [r2 < 0] sub-case, by reduction to positive [r2] via [Z.quot_opp_opp]
    and the [c1 ↔ -c1] bijection on γ. *)
Lemma cong_quot_best_const_divides_ndr1_neg r1 m1 r2 :
  r2 < 0 -> m1 <> 0 -> (r2 | m1) -> ~(r2 | r1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hm1 Hdiv Hnd.
  have Hr2_ne : r2 <> 0 by lia.
  have Hr2' : 0 < -r2 by lia.
  have Hdiv' : (-r2 | m1) by case: Hdiv => [k Hk]; exists (-k); lia.
  have Hnd' : ~(-r2 | -r1).
  { move=> [k Hk]. apply: Hnd. by exists k; lia. }
  have Hset :
    collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
      (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))
    ⊆⊇
    collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
      (γ[cong_ad] (-r1, m1)) (γ[cong_ad] (-r2, 0)).
  { split.
    - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]].
      exists (-c2), (-c1).
      split; [|split; [|split]].
      + unfold_set. unfold_set in Ha. case: Ha => [k Hk].
        exists (-k). lia.
      + unfold_set. unfold_set in Hb. case: Hb => [k Hk].
        exists 0. nia.
      + lia.
      + by rewrite (Z.quot_opp_opp _ _ Hne).
    - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]].
      exists (-c2), (-c1).
      split; [|split; [|split]].
      + unfold_set. unfold_set in Ha. case: Ha => [k Hk].
        exists (-k). lia.
      + unfold_set. unfold_set in Hb. case: Hb => [k Hk].
        exists 0. nia.
      + lia.
      + have Hne' : -c1 <> 0 by lia.
        rewrite -(Z.quot_opp_opp (-c2) (-c1) Hne').
        by rewrite !Z.opp_involutive. }
  apply: best_abstraction_equiv; last by symmetry; exact: Hset.
  exact: cong_quot_best_const_divides_ndr1_pos _ _ _ Hr2' Hm1 Hdiv' Hnd'.
Qed.

(** nonconstant_divisor for quot, [m1 > 0] sub-case.

    Strategy: pick a large positive c2 ∈ γ(r2,m2) with [c2 ≥ m1 + 2].
    Then find c1_a ∈ γ(r1,m1) ∩ [c2, 2c2) and c1_b ∈ γ(r1,m1) ∩ [0, m1).
    Both intervals have length ≥ m1 so γ-membership is guaranteed;
    [Z.quot c1_a c2 = 1] (nonneg, in [c2, 2c2)), [Z.quot c1_b c2 = 0]
    (nonneg, in [0, c2)). So {0, 1} ⊆ partial quot set and m' ∣ 1. *)
Lemma cong_quot_best_nonconstant_divisor_m1_pos r1 m1 r2 m2 :
  m2 <> 0 -> 0 < m1 ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2 Hm1.
  have Hm1_ne : m1 <> 0 by lia.
  have Hm2_abs : 1 <= Z.abs m2.
  { have := Z.abs_nonneg m2. case: (Z.abs_spec m2); lia. }
  have Hsgn_mul : Z.sgn m2 * m2 = Z.abs m2.
  { have := Z.abs_sgn m2. nia. }
  pose A := Z.abs r2 + m1 + 2.
  have HA : m1 + 2 <= A.
  { rewrite /A. have := Z.abs_nonneg r2. lia. }
  pose c2 := r2 + A * Z.sgn m2 * m2.
  have Hr2_abs : - Z.abs r2 <= r2 by case: (Z.abs_spec r2); lia.
  have Hc2_eq : c2 = r2 + A * Z.abs m2.
  { rewrite /c2. have := Hsgn_mul. nia. }
  have Hc2_bounds : m1 + 2 <= c2 by rewrite Hc2_eq /A; nia.
  have Hc2_pos : 0 < c2 by lia.
  have Hc2_in : c2 ∈ γ[cong_ad] (r2, m2)
    by unfold_set; exists (A * Z.sgn m2); rewrite /c2; ring.
  have Hc2_ne : c2 <> 0 by lia.
  (* c1_b := r1 mod m1, nonneg and < m1 ≤ c2. *)
  pose k_b := -(r1 / m1).
  pose c1_b := r1 + k_b * m1.
  have Hc1b_eq : c1_b = r1 mod m1.
  { rewrite /c1_b /k_b.
    have := Z.div_mod r1 m1 Hm1_ne. lia. }
  have Hc1b_bounds : 0 <= c1_b < m1
    by rewrite Hc1b_eq; exact: Z.mod_pos_bound.
  have Hc1b_in : c1_b ∈ γ[cong_ad] (r1, m1)
    by unfold_set; exists k_b; rewrite /c1_b; lia.
  (* c1_a := r1 + k_a*m1 with c2 ≤ c1_a < c2 + m1 < 2*c2. *)
  pose k_a := (c2 - r1 + m1 - 1) / m1.
  pose c1_a := r1 + k_a * m1.
  have Hc1a_bounds : c2 <= c1_a < c2 + m1.
  { rewrite /c1_a /k_a.
    have := Z.div_mod (c2 - r1 + m1 - 1) m1 Hm1_ne.
    have := Z.mod_pos_bound (c2 - r1 + m1 - 1) m1 Hm1. nia. }
  have Hc1a_ubound : c1_a < 2 * c2 by lia.
  have Hc1a_pos : 0 < c1_a by lia.
  have Hc1a_in : c1_a ∈ γ[cong_ad] (r1, m1)
    by unfold_set; exists k_a; rewrite /c1_a; lia.
  apply: WithBottom.BestAbstraction_NotBot.
  - (* Non-empty: 0 ∈ partial set via Z.quot c1_b c2 = 0. *)
    exists 0, c1_b, c2. split; [exact Hc1b_in|].
    split; [exact Hc2_in|]. split; [exact Hc2_ne|].
    rewrite (Z.quot_div_nonneg _ _ (ltac:(lia) : 0 <= c1_b) Hc2_pos).
    apply: Z.div_small. lia.
  - split.
    + move=> c _. unfold_set. exact: Z.divide_1_l.
    + move=> [r' m'] HS.
      have H0_in : 0 ∈ collecting_binary_forward_partial
                         (fun _ c1 => c1 <> 0) Z.quot
                         (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)).
      { exists c1_b, c2.
        split; [exact Hc1b_in|].
        split; [exact Hc2_in|]. split; [exact Hc2_ne|].
        rewrite (Z.quot_div_nonneg _ _ (ltac:(lia) : 0 <= c1_b) Hc2_pos).
        apply: Z.div_small. lia. }
      have H1_in : 1 ∈ collecting_binary_forward_partial
                         (fun _ c1 => c1 <> 0) Z.quot
                         (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)).
      { exists c1_a, c2.
        split; [exact Hc1a_in|].
        split; [exact Hc2_in|]. split; [exact Hc2_ne|].
        rewrite (Z.quot_div_nonneg _ _ (ltac:(lia) : 0 <= c1_a) Hc2_pos).
        symmetry. apply: (Z.div_unique _ _ 1 (c1_a - c2)); lia. }
      have := HS _ H0_in. unfold_set => H0'.
      have := HS _ H1_in. unfold_set => H1'.
      have Hone : (m' | 1).
      { have H := Z.divide_sub_r _ _ _ H1' H0'.
        by have -> : 1 = (1 - r') - (0 - r') by ring. }
      split; first exact: Hone.
      exact: H0'.
Qed.

(** Any sign of m1 (nonzero): reduce m1 < 0 to m1 > 0 via γ-symmetry. *)
Lemma cong_quot_best_nonconstant_divisor_m1_nz (r1 m1 r2 m2 : Z) :
  m2 <> 0 -> m1 <> 0 ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2 Hm1.
  case: (Z_lt_le_dec 0 m1) => Hm1_sgn.
  - exact: cong_quot_best_nonconstant_divisor_m1_pos.
  - have Hmm1 : 0 < -m1 by lia.
    apply: best_abstraction_equiv;
      last (symmetry; apply: collecting_quot_gamma_cong_l; exact: cong_gamma_sym_m).
    exact: cong_quot_best_nonconstant_divisor_m1_pos _ _ _ _ Hm2 Hmm1.
Qed.

(** 0 is always in the partial quot set when m1 = 0 and m2 ≠ 0:
    pick any nonzero c2 ∈ γ(r2, m2) of magnitude greater than |r1|, and
    Z.quot r1 c2 = 0. *)
Lemma zero_in_quot_set_m1_zero r1 r2 m2 :
  m2 <> 0 ->
  0 ∈ collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
        (γ[cong_ad] (r1, 0)) (γ[cong_ad] (r2, m2)).
Proof.
  move=> Hm2.
  have Hm2_abs : 1 <= Z.abs m2.
  { have := Z.abs_nonneg m2. case: (Z.abs_spec m2); lia. }
  have Hsgn_mul : Z.sgn m2 * m2 = Z.abs m2 by have := Z.abs_sgn m2; nia.
  pose A := Z.abs r1 + Z.abs r2 + 1.
  pose c2 := r2 + A * Z.sgn m2 * m2.
  have HA : 1 <= A.
  { rewrite /A. have := Z.abs_nonneg r1. have := Z.abs_nonneg r2. lia. }
  have Hr2_abs : - Z.abs r2 <= r2 by case: (Z.abs_spec r2); lia.
  have Hc2_eq : c2 = r2 + A * Z.abs m2 by rewrite /c2; nia.
  have Hc2_bounds : Z.abs r1 + 1 <= c2 by rewrite Hc2_eq /A; nia.
  have Hr1_abs : Z.abs r1 >= 0 by have := Z.abs_nonneg r1; lia.
  have Hc1_abs : - Z.abs r1 <= r1 <= Z.abs r1 by case: (Z.abs_spec r1); lia.
  have Hc2_pos : 0 < c2 by lia.
  have Hc2_ne : c2 <> 0 by lia.
  have Hc2_in : c2 ∈ γ[cong_ad] (r2, m2)
    by unfold_set; exists (A * Z.sgn m2); rewrite /c2; ring.
  exists r1, c2. split; [by exists 0; lia|].
  split; [exact Hc2_in|]. split; [exact Hc2_ne|].
  apply/Z.quot_small_iff => //.
  have -> : Z.abs c2 = c2 by case: (Z.abs_spec c2); lia.
  case: (Z.abs_spec r1); lia.
Qed.

(** Best abstraction for the m1 = 0 case (any r1), using the refined
    [cong_quot] result [(0, quot_gcd_compute r1 r2 m2)]. *)
Lemma cong_quot_best_m1_zero r1 r2 m2 :
  m2 <> 0 ->
  BestAbstraction (A:=WithBottom.ad cong_ad)
    (WithBottom.NotBot (0, quot_gcd_compute r1 r2 m2))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, 0)) (γ[cong_ad] (r2, m2))).
Proof.
  move=> Hm2.
  set m := quot_gcd_compute r1 r2 m2.
  split.
  - (* Overapproximates *)
    move=> c0 [c1 [c2 [Hc1 [Hc2 [Hne Hd]]]]].
    unfold_set in Hc1. case: Hc1 => [k Hk].
    have Hc1_eq : c1 = r1 by nia.
    subst c0. unfold_set.
    have [j Hj] : (m | Z.quot c1 c2).
    { rewrite Hc1_eq. apply: quot_gcd_compute_divides => //. }
    by exists j; lia.
  - move=> [|[r' m']] Ha'.
    + (* a' = Bot: contradicted by 0 ∈ S *)
      exfalso. have H0 := zero_in_quot_set_m1_zero r1 r2 m2 Hm2.
      have := Ha' _ H0. by rewrite propset_elem_of_iff.
    + simpl. split.
      * (* m' | m *)
        have H0 := zero_in_quot_set_m1_zero r1 r2 m2 Hm2.
        have := Ha' _ H0. unfold_set => [[j Hj]].
        (* Hj : 0 - r' = j * m'. So m' | r'. *)
        have Hmr' : (m' | r') by exists (-j); lia.
        apply: quot_gcd_compute_optimal => //.
        move=> c Hc_in Hc_nz.
        have Hin : Z.quot r1 c ∈
          collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
            (γ[cong_ad] (r1, 0)) (γ[cong_ad] (r2, m2)).
        { exists r1, c. split; [by exists 0; lia|].
          split; [exact Hc_in|]. split; [exact Hc_nz | reflexivity]. }
        have := Ha' _ Hin. unfold_set => [[j2 Hj2]].
        case: Hmr' => [l Hl].
        exists (j2 + l). lia.
      * (* m' | 0 - r' = -r' *)
        have H0 := zero_in_quot_set_m1_zero r1 r2 m2 Hm2.
        have := Ha' _ H0. by unfold_set => [[j Hj]]; exists j; lia.
Qed.

Lemma cong_quot_best_const_neg r1 m1 r2 :
  r2 < 0 -> ~(r2 | m1) ->
  BestAbstraction (A:=WithBottom.ad cong_ad) (WithBottom.NotBot (0, 1))
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
       (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))).
Proof.
  move=> Hr2 Hnd.
  have Hr2_ne : r2 <> 0 by lia.
  have Hr2' : 0 < -r2 by lia.
  have Hnd' : ~(-r2 | m1).
  { move=> [k Hk]. apply: Hnd. by exists (-k); lia. }
  (* Build set equivalence: divisor r2 ↔ dividend-flip to -r2. *)
  have Hset :
    collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
      (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, 0))
    ⊆⊇
    collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot
      (γ[cong_ad] (-r1, m1)) (γ[cong_ad] (-r2, 0)).
  { split.
    - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]].
      exists (-c2), (-c1).
      split; [|split; [|split]].
      + unfold_set. unfold_set in Ha. case: Ha => [k Hk].
        exists (-k). lia.
      + unfold_set. unfold_set in Hb. case: Hb => [k Hk].
        exists 0. nia.
      + lia.
      + by rewrite (Z.quot_opp_opp _ _ Hne).
    - move=> c [c2 [c1 [Ha [Hb [Hne Hd]]]]].
      exists (-c2), (-c1).
      split; [|split; [|split]].
      + unfold_set. unfold_set in Ha. case: Ha => [k Hk].
        exists (-k). lia.
      + unfold_set. unfold_set in Hb. case: Hb => [k Hk].
        exists 0. nia.
      + lia.
      + have Hne' : -c1 <> 0 by lia.
        rewrite -(Z.quot_opp_opp (-c2) (-c1) Hne').
        by rewrite !Z.opp_involutive. }
  apply: best_abstraction_equiv; last by symmetry; exact: Hset.
  exact: cong_quot_best_const_pos _ _ _ Hr2' Hnd'.
Qed.

(** Aggregate: [cong_quot] is a best abstraction for [Z.quot] under
    partial semantics (divisor ≠ 0). Dispatches on the [if]-structure of
    [cong_quot]:
    - divisor_zero (r2 = m2 = 0) → Bot
    - const_divides (m2 = 0, r2 ≠ 0, m1 = 0 ∨ (r2|m1 ∧ r2|r1)) → exact
    - const_pos/neg (m2 = 0, r2 ≠ 0, r2 ∤ m1) → top
    - const_divides_ndr1_pos/neg (m2 = 0, r2 ≠ 0, r2|m1 ∧ r2∤r1 ∧ m1≠0) → top
    - dividend_zero (m2 ≠ 0, r1 = m1 = 0) → exact
    - nonconstant_divisor (m2 ≠ 0, otherwise) → top (stub) *)
Lemma cong_quot_best :
  binary_best cong_ad cong_ad (WithBottom.ad cong_ad) cong_quot
    (collecting_binary_forward_partial (fun _ c1 => c1 <> 0) Z.quot).
Proof.
  move=> a2 a1.
  move: a2 a1 => [r1 m1] [r2 m2].
  rewrite /cong_quot.
  case Hm2 : (m2 =? 0).
  - move/Z.eqb_eq: Hm2 => ->.
    case Hr2 : (r2 =? 0).
    + move/Z.eqb_eq: Hr2 => ->. exact: cong_quot_best_divisor_zero.
    + move/Z.eqb_neq: Hr2 => Hr2.
      case Hcond : ((m1 =? 0) || ((m1 mod r2 =? 0) && (r1 mod r2 =? 0))).
      * (* const_divides *)
        apply: cong_quot_best_const_divides => //.
        move: Hcond => /orP [/Z.eqb_eq ->|/andP [/Z.eqb_eq Hmm /Z.eqb_eq Hrm]].
        -- by left.
        -- right. split; by apply/Z.mod_divide.
      * (* top: extract m1 ≠ 0 and NOT(r2|m1 ∧ r2|r1). *)
        have Hm1 : m1 <> 0.
        { move=> H. move: Hcond. by rewrite H /=. }
        have Hcond2 : ~((r2 | m1) /\ (r2 | r1)).
        { move=> [Hd1 Hd2]. move: Hcond.
          have Hb1 : m1 mod r2 = 0 by apply/Z.mod_divide.
          have Hb2 : r1 mod r2 = 0 by apply/Z.mod_divide.
          by rewrite Hb1 Hb2 /= orb_true_r. }
        case Hdiv_m1 : (m1 mod r2 =? 0); last first.
        -- (* r2 ∤ m1: const_pos or const_neg *)
           move/Z.eqb_neq: Hdiv_m1 => Hmm.
           have Hnd : ~(r2 | m1).
           { move=> H. apply: Hmm. by apply/Z.mod_divide. }
           case: (Z_lt_le_dec 0 r2) => Hr2sgn.
           ++ exact: cong_quot_best_const_pos.
           ++ have Hr2lt : r2 < 0 by lia.
              exact: cong_quot_best_const_neg.
        -- (* r2 | m1 ∧ r2 ∤ r1 (must hold since const_divides failed): const_divides_ndr1 *)
           move/Z.eqb_eq: Hdiv_m1 => Hmm.
           have Hdiv_m1' : (r2 | m1) by apply/Z.mod_divide.
           have Hdiv_r1 : ~(r2 | r1).
           { move=> H. exact: Hcond2 (conj Hdiv_m1' H). }
           case: (Z_lt_le_dec 0 r2) => Hr2sgn.
           ++ exact: cong_quot_best_const_divides_ndr1_pos.
           ++ have Hr2lt : r2 < 0 by lia.
              exact: cong_quot_best_const_divides_ndr1_neg.
  - move/Z.eqb_neq: Hm2 => Hm2.
    case Hm1 : (m1 =? 0).
    + move/Z.eqb_eq: Hm1 => ->. exact: cong_quot_best_m1_zero.
    + move/Z.eqb_neq: Hm1 => Hm1.
      exact: cong_quot_best_nonconstant_divisor_m1_nz.
Qed.

(** * Less-or-equal abstraction [cong_le].

    The result of [Z.leb a b] for [a ∈ γ(r1, m1)], [b ∈ γ(r2, m2)] is a
    set of booleans, abstracted by [quadrivalent]. When both inputs are
    constants ([m1 = 0 ∧ m2 = 0]), the comparison is exact: [Z.leb r1 r2].
    Otherwise at least one of γ(r1,m1), γ(r2,m2) is unbounded above and
    below, so both [true] and [false] are realised, giving [QTop] —
    again exact. *)

Definition cong_le (a1 a2 : Z * Z) : quadrivalent :=
  let (r1, m1) := a1 in
  let (r2, m2) := a2 in
  if (m1 =? 0) && (m2 =? 0) then
    if r1 <=? r2 then QTrue else QFalse
  else QTop.

Local Instance qv_exact_order : ExactOrder Quadrivalent.qv.
Proof. move=> q1 q2. exact: qv_sqsubseteq_exact. Qed.

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

Lemma cong_le_exact r1 m1 r2 m2 :
  ExactlyRepresents (A:=Quadrivalent.qv)
    (cong_le (r1, m1) (r2, m2))
    (collecting_binary_forward Z.leb (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  rewrite /cong_le.
  have HS_bool : forall b, b ∈ collecting_binary_forward Z.leb
                              (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2)) ->
                            b = true \/ b = false.
  { move=> b _. by case: b; [left|right]. }
  case Hm1 : (m1 =? 0); case Hm2 : (m2 =? 0); rewrite /=.
  - (* m1 = 0 ∧ m2 = 0: γ(r1,0) = {r1}, γ(r2,0) = {r2}, S = {Z.leb r1 r2}. *)
    move/Z.eqb_eq: Hm1 => Hm1z. move/Z.eqb_eq: Hm2 => Hm2z. subst m1 m2.
    have Ha_eq : forall a, a ∈ γ[cong_ad] (r1, 0) -> a = r1
      by move=> a; exact (proj1 (gamma_singleton _ _)).
    have Hb_eq : forall b, b ∈ γ[cong_ad] (r2, 0) -> b = r2
      by move=> b; exact (proj1 (gamma_singleton _ _)).
    case Hcmp : (r1 <=? r2); split.
    + move=> b. rewrite in_QTrue_iff => ->.
      exists r1, r2. split; [|split].
      * by apply/gamma_singleton.
      * by apply/gamma_singleton.
      * by [].
    + move=> b [a [b' [Ha [Hb' Heq]]]].
      rewrite (Ha_eq _ Ha) (Hb_eq _ Hb') in Heq.
      rewrite in_QTrue_iff. by rewrite -Heq.
    + move=> b. rewrite in_QFalse_iff => ->.
      exists r1, r2. split; [|split].
      * by apply/gamma_singleton.
      * by apply/gamma_singleton.
      * by [].
    + move=> b [a [b' [Ha [Hb' Heq]]]].
      rewrite (Ha_eq _ Ha) (Hb_eq _ Hb') in Heq.
      rewrite in_QFalse_iff. by rewrite -Heq.
  - (* m1 = 0, m2 ≠ 0: γ(r1,0) = {r1}, γ(r2,m2) unbounded.  Result QTop, exact. *)
    move/Z.eqb_eq: Hm1 => Hm1z. move/Z.eqb_neq: Hm2 => Hm2nz. subst m1.
    split.
    + (* γ(QTop) ⊆ S: every bool is realised. *)
      move=> b _.
      case: b.
      * have [b' [Hb'_in Hb'_le]] := cong_unbounded_above r2 m2 r1 Hm2nz.
        exists r1, b'. split; [|split].
        -- by apply/gamma_singleton.
        -- exact: Hb'_in.
        -- by apply/Z.leb_le.
      * have [b' [Hb'_in Hb'_le]] := cong_unbounded_below r2 m2 (r1 - 1) Hm2nz.
        exists r1, b'. split; [|split].
        -- by apply/gamma_singleton.
        -- exact: Hb'_in.
        -- by apply/Z.leb_gt; lia.
    + by move=> b _; case: b.
  - (* m1 ≠ 0, m2 = 0. *)
    move/Z.eqb_neq: Hm1 => Hm1nz. move/Z.eqb_eq: Hm2 => Hm2z. subst m2.
    split.
    + move=> b _.
      case: b.
      * have [a [Ha_in Ha_le]] := cong_unbounded_below r1 m1 r2 Hm1nz.
        exists a, r2. split; [|split].
        -- exact: Ha_in.
        -- by apply/gamma_singleton.
        -- by apply/Z.leb_le.
      * have [a [Ha_in Ha_le]] := cong_unbounded_above r1 m1 (r2 + 1) Hm1nz.
        exists a, r2. split; [|split].
        -- exact: Ha_in.
        -- by apply/gamma_singleton.
        -- by apply/Z.leb_gt; lia.
    + by move=> b _; case: b.
  - (* m1 ≠ 0, m2 ≠ 0. *)
    move/Z.eqb_neq: Hm1 => Hm1nz. move/Z.eqb_neq: Hm2 => Hm2nz.
    split.
    + move=> b _.
      case: b.
      * have [a [Ha_in _]] := cong_unbounded_above r1 m1 0 Hm1nz.
        have [b' [Hb'_in Hb'_le]] := cong_unbounded_above r2 m2 a Hm2nz.
        exists a, b'. split; [|split].
        -- exact: Ha_in.
        -- exact: Hb'_in.
        -- by apply/Z.leb_le.
      * have [a [Ha_in _]] := cong_unbounded_above r1 m1 0 Hm1nz.
        have [b' [Hb'_in Hb'_le]] := cong_unbounded_below r2 m2 (a - 1) Hm2nz.
        exists a, b'. split; [|split].
        -- exact: Ha_in.
        -- exact: Hb'_in.
        -- by apply/Z.leb_gt; lia.
    + by move=> b _; case: b.
Qed.

Lemma cong_le_best r1 m1 r2 m2 :
  BestAbstraction (A:=Quadrivalent.qv)
    (cong_le (r1, m1) (r2, m2))
    (collecting_binary_forward Z.leb (γ[cong_ad] (r1, m1)) (γ[cong_ad] (r2, m2))).
Proof.
  apply: is_alpha_is_best_abstraction.
  apply: exact_is_is_alpha. exact: cong_le_exact.
Qed.
