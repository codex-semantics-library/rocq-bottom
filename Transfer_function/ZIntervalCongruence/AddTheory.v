(* AddTheory.v - [Z.add] transfer function for the ZIntervalCongruence
   single-value abstraction: the operation [add] (the raw transfer
   function [add_raw] from [OpsComp]), its soundness, and its
   α-completeness. Split out of ZIntervalCongruence.v. *)

(* STATUS: add: sound + best (α-complete); NOT γ-exact
   ([add_reduced_not_gamma_exact]).

   [add_raw] lives in the computational layer ([OpsComp.v]). The
   user-facing operation is [add_reduced], typed on the *non-bottom*
   maximally-reduced domain [non_bottom_zic]: since [add] of two non-empty
   sets is never empty, that domain is its natural home and there are no
   bottom cases. [add_reduced_best] shows the raw result is already the
   best abstraction of the collecting sum (α-complete), so no [reduce] is
   needed. Bottom-carrying composition is the caller's concern (the
   convention keeps [add]'s arguments and result non-bottom). *)

From Stdlib Require Import ZArith Lia.
Require Import ssreflect ssrbool.
Require Import
  base Abstraction AbstractLattice
  AbstractionCombination
  Z_interval Congruence
  ZIntervalCongruence
  Transfer_function.Congruence.AddTheory
  Transfer_function.ZIntervalCongruence.OpsComp.

Open Scope Z_scope.

(** ** [add] on the plain product base [prod_ajsl] (L0).

    The same [add_raw], but stated over [prod_ajsl] (carrier identical
    to [collapsed_ad]; γ identical since [CollapsedBottom] only changes the
    order). These are the bridges the L1/L2 layers consume. *)

Lemma add_raw_sound_prod :
  binary_overapproximation prod_ajsl prod_ajsl prod_ajsl add_raw
    (collecting_binary_forward Z.add).
Proof.
  move=> [i2 c2] [i1 c1] c0 [d2 [d1 [Hd2 [Hd1 Hc0]]]].
  have [Hd2_i Hd2_c] := Hd2.
  have [Hd1_i Hd1_c] := Hd1.
  split.
  - apply: (interval_add_sound i2 i1). by exists d2, d1.
  - apply: (cong_add_sound c2 c1). by exists d2, d1.
Qed.

(** Best-abstraction split over the plain product, directly via
    [Conjunction.is_alpha_pair_iff] — no [CollapsedBottom] hops. *)
Lemma prod_is_alpha_split (i : interval) (c : Z * Z) (S : ℘ Z) :
  IsAlpha (A:=prod_ajsl) (i, c) S <->
  IsAlpha (A:=itv) i S /\ IsAlpha (A:=cong_ad) c S.
Proof. exact: (Conjunction.is_alpha_pair_iff itv cong_ajsl i c S). Qed.

Lemma add_raw_alpha_complete_prod (a2 a1 : prod_ajsl) (S2 S1 : ℘ Z) :
  IsAlpha (A:=prod_ajsl) a2 S2 -> IsAlpha (A:=prod_ajsl) a1 S1 ->
  (exists c, c ∈ S1) -> (exists c, c ∈ S2) ->
  IsAlpha (A:=prod_ajsl) (add_raw a2 a1)
    (collecting_binary_forward Z.add S2 S1).
Proof.
  move: a2 a1 => [i2 c2] [i1 c1] Ha2 Ha1 Hne1 Hne2.
  have [Hi2 Hc2] := proj1 (prod_is_alpha_split i2 c2 S2) Ha2.
  have [Hi1 Hc1] := proj1 (prod_is_alpha_split i1 c1 S1) Ha1.
  rewrite /add_raw /=.
  apply/(prod_is_alpha_split (interval_add i2 i1) (cong_add c2 c1)).
  split.
  - exact: interval_add_alpha_complete i2 i1 S2 S1 Hne2 Hne1 Hi2 Hi1.
  - exact: cong_add_alpha_complete c2 c1 S2 S1 Hc2 Hc1.
Qed.

(** ** [add] preserves maximal reduction (the headline result).

    Core lemma, stated at the base [prod_ajsl]; both L2 and L3 consume
    it. The non-emptiness hypotheses are exactly what
    [add_raw_alpha_complete_prod] needs, so there are no bottom cases. *)
Lemma add_raw_preserves_mr (a2 a1 : prod_ajsl) :
  nonempty_pred a2 -> nonempty_pred a1 ->
  MaximallyReduced (A:=prod_ajsl) a2 -> MaximallyReduced (A:=prod_ajsl) a1 ->
  MaximallyReduced (A:=prod_ajsl) (add_raw a2 a1).
Proof.
  move=> Hne2 Hne1 Hmr2 Hmr1.
  have Ha2 : IsAlpha (A:=prod_ajsl) a2 (γ[prod_ajsl] a2)
    by apply/is_alpha_iff_best_abstraction.
  have Ha1 : IsAlpha (A:=prod_ajsl) a1 (γ[prod_ajsl] a1)
    by apply/is_alpha_iff_best_abstraction.
  apply: (is_alpha_maximally_reduced (A:=prod_ajsl) (add_raw a2 a1)
            (collecting_binary_forward Z.add (γ[prod_ajsl] a2) (γ[prod_ajsl] a1))).
  exact: (add_raw_alpha_complete_prod a2 a1 _ _ Ha2 Ha1 Hne1 Hne2).
Qed.

(** ** L1 ([nonempty_prod_ajsl]) and L2 ([non_bottom_zic]) typed operations. *)

(** [add] lifted to the γ-non-empty subtype, via the generic
    [NonEmpty] machinery; non-emptiness is preserved because [add_raw]
    is a sound over-approximation of a total function. Extracts to
    [add_raw]. *)
Definition add_nonempty : nonempty_prod_ajsl -> nonempty_prod_ajsl -> nonempty_prod_ajsl :=
  NonEmpty.nonempty_lift_total_binary prod_ajsl nonempty_pred
    (fun a => iff_refl _) add_raw Z.add (Hsound := add_raw_sound_prod).

(** [mr_nonempty_iff_prod] (maximal reduction coincides on the
    [nonempty_prod_ajsl] subtype and the base [prod_ajsl]) lives in
    [ZIntervalCongruence]. *)

(** [add] preserves maximal reduction on [nonempty_prod_ajsl] — thin wrapper
    of [add_raw_preserves_mr] through the bridge. No bottom cases. *)
Lemma add_reduced_closure (x y : nonempty_prod_ajsl) :
  MaximallyReduced (A:=nonempty_prod_ajsl) x -> MaximallyReduced (A:=nonempty_prod_ajsl) y ->
  MaximallyReduced (A:=nonempty_prod_ajsl) (add_nonempty x y).
Proof.
  move: x y => [ax px] [ay py] Hmrx Hmry.
  apply/(mr_nonempty_iff_prod (add_raw ax ay)).
  apply: add_raw_preserves_mr.
  - exact: px.
  - exact: py.
  - exact: (proj1 (mr_nonempty_iff_prod ax px) Hmrx).
  - exact: (proj1 (mr_nonempty_iff_prod ay py) Hmry).
Qed.

(** [add] on the maximally-reduced subtype [non_bottom_zic] (L2). This is
    the typed operation through which "[add] returns a maximally-reduced
    element when given maximally-reduced ones" holds. Extracts to
    [add_raw]. *)
Definition add_reduced (x y : non_bottom_zic) : non_bottom_zic :=
  exist _ (add_nonempty (`x) (`y))
    (add_reduced_closure (`x) (`y) (proj2_sig x) (proj2_sig y)).

(** [add_raw] is the *best* abstraction of the collecting sum on the
    plain product, whenever its operands are non-empty and maximally
    reduced. This is [add_raw_alpha_complete_prod] read through
    [is_alpha_is_best_abstraction]. *)
Lemma add_raw_best_prod (a2 a1 : prod_ajsl) :
  nonempty_pred a2 -> nonempty_pred a1 ->
  MaximallyReduced (A:=prod_ajsl) a2 -> MaximallyReduced (A:=prod_ajsl) a1 ->
  BestAbstraction (A:=prod_ajsl) (add_raw a2 a1)
    (collecting_binary_forward Z.add (γ[prod_ajsl] a2) (γ[prod_ajsl] a1)).
Proof.
  move=> Hne2 Hne1 Hmr2 Hmr1.
  have Ha2 : IsAlpha (A:=prod_ajsl) a2 (γ[prod_ajsl] a2)
    by apply/is_alpha_iff_best_abstraction.
  have Ha1 : IsAlpha (A:=prod_ajsl) a1 (γ[prod_ajsl] a1)
    by apply/is_alpha_iff_best_abstraction.
  apply: is_alpha_is_best_abstraction.
  exact: (add_raw_alpha_complete_prod a2 a1 _ _ Ha2 Ha1 Hne1 Hne2).
Qed.

(** [add_reduced] is sound on the non-bottom maximally-reduced domain.
    Reduces to [add_raw_sound_prod] since [γ] and [add_reduced]'s
    carrier pass through the two [Subset] layers unchanged. *)
Lemma add_reduced_sound :
  binary_overapproximation non_bottom_zic non_bottom_zic non_bottom_zic add_reduced
    (collecting_binary_forward Z.add).
Proof.
  move=> [[a2 n2] m2] [[a1 n1] m1] c Hc.
  exact: (add_raw_sound_prod a2 a1 c Hc).
Qed.

(** Headline: [add_reduced] computes the *best* abstraction of the
    collecting sum. On the non-bottom domain [non_bottom_zic] every
    element is non-empty and maximally reduced (structurally), so there
    are no bottom/empty side conditions: this is the universal
    [binary_best], lifted from [add_raw_best_prod] through the [Subset]
    layers (which leave [γ] and [⊑] unchanged). *)
Lemma add_reduced_best :
  binary_best non_bottom_zic non_bottom_zic non_bottom_zic add_reduced
    (collecting_binary_forward Z.add).
Proof.
  move=> [[a2 n2] m2] [[a1 n1] m1].
  have Hmr2 := proj1 (mr_nonempty_iff_prod a2 n2) m2.
  have Hmr1 := proj1 (mr_nonempty_iff_prod a1 n1) m1.
  have [Hover Hopt] :=
    proj1 (best_abstraction_iff _ _) (add_raw_best_prod a2 a1 n2 n1 Hmr2 Hmr1).
  apply/best_abstraction_iff. split.
  - exact: Hover.
  - move=> [[a' n'] m'] Ha'. exact: (Hopt a' Ha').
Qed.

(** [add] is non-bottom in and non-bottom out (per the transfer-function
    convention): the user-facing operation is [add_reduced] above, on the
    non-bottom maximally-reduced domain [non_bottom_zic]. Bottom
    short-circuiting, when composing with operations that can be empty, is
    the caller's responsibility — there is no [zic]-typed [add]. *)

(** ** Non-exactness of the (best) addition.

    [add_reduced] computes the *best* abstraction of the collecting sum
    ([add_reduced_best]), yet it is not γ-exact ([binary_exact]): the
    interval × congruence domain simply cannot represent every collecting
    sum exactly.

    Counterexample [{0,8} + {0,3} = {0,3,8,11}]. The non-exactness is a
    property of the *domain*, not of [add_reduced], so we factor it that
    way (general → specific):

    - [quad_enclosure_has_1] — the structural core: every interval ×
      congruence enclosure of [{0,3,8,11}] also admits [1] (the interval
      must cover [[0,11]]; the modulus must divide [gcd 3 8 = 1], so the
      congruence is all of ℤ).
    - [quad_set_not_representable] — hence [{0,3,8,11}] is not in the image
      of [γ]: no element has it as exact concretization.
    - [add_reduced_not_gamma_exact] — the corollary: were [add_reduced]
      exact, its result would exactly represent the collecting sum
      [= {0,3,8,11}], contradicting the above. *)

Section AddNotExact.

(** The concrete set [{0,3,8,11}] — the collecting sum of [{0,8}] and
    [{0,3}] (proved equal in [add_collecting_quad]). The whole argument is
    that this set is not in the image of [γ]. *)
Definition quad_set : ℘ Z := {[ x | x = 0 \/ x = 3 \/ x = 8 \/ x = 11 ]}.

(** *** Structural core.

    Every interval × congruence pair that over-approximates [{0,3,8,11}]
    also admits [1]: the interval contains [0] and [11] hence (by
    [itv_convex]) the whole of [[0,11] ∋ 1]; and the modulus divides both
    [3] and [8], hence [gcd 3 8 = 1], so the congruence class is all of ℤ. *)
Lemma quad_enclosure_has_1 (i : interval) (c : Z * Z) :
  quad_set ⊆ γ[prod_ajsl] (i, c) -> (1:Z) ∈ γ[prod_ajsl] (i, c).
Proof.
  case: i => l h. case: c => r m. move=> Hsub.
  have mem : forall k : Z, k = 0 \/ k = 3 \/ k = 8 \/ k = 11 ->
              k ∈ γ[prod_ajsl] ((l, h), (r, m)).
  { move=> k Hk. apply: Hsub. rewrite /quad_set. by apply/propset_elem_of_iff. }
  have [H0i  H0c]  := mem 0  (or_introl eq_refl).
  have [H3i  H3c]  := mem 3  (or_intror (or_introl eq_refl)).
  have [H8i  H8c]  := mem 8  (or_intror (or_intror (or_introl eq_refl))).
  have [H11i H11c] := mem 11 (or_intror (or_intror (or_intror eq_refl))).
  have H0c' : (m | 0 - r) := H0c.
  have H3c' : (m | 3 - r) := H3c.
  have H8c' : (m | 8 - r) := H8c.
  (* modulus divides gcd(3,8) = 1, so the congruence covers all of ℤ *)
  have Hm3 : (m | 3).
  { have H := Z.divide_sub_r m (3 - r) (0 - r) H3c' H0c'.
    by replace (3 - r - (0 - r)) with 3 in H by lia. }
  have Hm8 : (m | 8).
  { have H := Z.divide_sub_r m (8 - r) (0 - r) H8c' H0c'.
    by replace (8 - r - (0 - r)) with 8 in H by lia. }
  have Hm1 : (m | 1).
  { have Hg := Z.gcd_greatest 3 8 m Hm3 Hm8.
    have e : Z.gcd 3 8 = 1 by []. by rewrite e in Hg. }
  split.
  - (* interval covers 1, by convexity between 0 and 11 *)
    apply: (itv_convex l h 0 11 1 H0i H11i); lia.
  - (* congruence: m | 1 - r, from m | 1 and m | 0 - r *)
    have Hadd := Z.divide_add_r m 1 (0 - r) Hm1 H0c'.
    have Hdiv : (m | 1 - r) by replace (1 - r) with (1 + (0 - r)) by lia.
    exact: Hdiv.
Qed.

(** *** Intermediate fact.

    [{0,3,8,11}] is not exactly representable: no interval × congruence
    element has it as its concretization. Such an element would
    over-approximate the set, hence (by [quad_enclosure_has_1]) admit [1];
    yet it would also be included in the set, forcing the absurd
    [1 ∈ {0,3,8,11}]. *)
Lemma quad_set_not_representable :
  ~ exists a : prod_ajsl, ExactlyRepresents (A := prod_ajsl) a quad_set.
Proof.
  move=> [[i c] Hrep]. have [Hfwd Hbwd] := Hrep.
  have H1 := quad_enclosure_has_1 i c Hbwd.
  have H1q : (1:Z) ∈ quad_set := Hfwd 1 H1.
  move: H1q; rewrite /quad_set => /propset_elem_of_iff [E|[E|[E|E]]]; lia.
Qed.

(** The two operands: [{0,8} = [0,8] ∩ (0+8ℤ)] and [{0,3} = [0,3] ∩ (0+3ℤ)],
    each an exact (two-point) representation. *)
Definition op08 : non_bottom_zic :=
  interval_cong_elt 0 8 0 8
    ltac:(lia) ltac:(by exists 0) ltac:(by exists 1) ltac:(lia).
Definition op03 : non_bottom_zic :=
  interval_cong_elt 0 3 0 3
    ltac:(lia) ltac:(by exists 0) ltac:(by exists 1) ltac:(lia).

(** The collecting sum of the two operands is exactly [{0,3,8,11}]:
    [γ op08 = {0,8}], [γ op03 = {0,3}], and their pairwise sums exhaust
    [{0,3,8,11}]. *)
Lemma add_collecting_quad :
  collecting_binary_forward Z.add (γ[non_bottom_zic] op08) (γ[non_bottom_zic] op03)
    ⊆⊇ quad_set.
Proof.
  (* Membership in each operand: "in range and on the class", both ways. *)
  have e08 : forall z, 0 <= z <= 8 -> (8 | z - 0) -> z ∈ γ[non_bottom_zic] op08.
  { move=> z Hb Hc. rewrite /op08. apply/interval_cong_elt_gammaE. by split. }
  have e03 : forall z, 0 <= z <= 3 -> (3 | z - 0) -> z ∈ γ[non_bottom_zic] op03.
  { move=> z Hb Hc. rewrite /op03. apply/interval_cong_elt_gammaE. by split. }
  have d08 : forall z, z ∈ γ[non_bottom_zic] op08 -> 0 <= z <= 8 /\ (8 | z - 0).
  { move=> z H. rewrite /op08 in H. by move/interval_cong_elt_gammaE: H => H. }
  have d03 : forall z, z ∈ γ[non_bottom_zic] op03 -> 0 <= z <= 3 /\ (3 | z - 0).
  { move=> z H. rewrite /op03 in H. by move/interval_cong_elt_gammaE: H => H. }
  rewrite /quad_set. split.
  - (* collecting ⊆ {0,3,8,11}: divide both summands out, then lia *)
    move=> c0 Hcol. unfold_set in Hcol.
    move: Hcol => [c2 [c1 [Hc2 [Hc1 <-]]]].
    move: (d08 _ Hc2) => [Hb2 [k2 Hk2]]. move: (d03 _ Hc1) => [Hb1 [k1 Hk1]].
    apply/propset_elem_of_iff. lia.
  - (* {0,3,8,11} ⊆ collecting: pick the summands for each value *)
    move=> c0 /propset_elem_of_iff [->|[->|[->|->]]]; unfold_set.
    + exists 0, 0. split; [by apply: e08; [lia | exists 0] |].
      split; [by apply: e03; [lia | exists 0] | by []].
    + exists 0, 3. split; [by apply: e08; [lia | exists 0] |].
      split; [by apply: e03; [lia | exists 1] | by []].
    + exists 8, 0. split; [by apply: e08; [lia | exists 1] |].
      split; [by apply: e03; [lia | exists 0] | by []].
    + exists 8, 3. split; [by apply: e08; [lia | exists 1] |].
      split; [by apply: e03; [lia | exists 1] | by []].
Qed.

(** *** Headline (corollary): the best addition is not γ-exact.

    Were [add_reduced] exact, [add_reduced op08 op03] would exactly
    represent the collecting sum [= {0,3,8,11}] (its carrier is a
    [prod_ajsl] element with that concretization), contradicting
    [quad_set_not_representable]. *)
Lemma add_reduced_not_gamma_exact :
  ~ binary_exact non_bottom_zic non_bottom_zic non_bottom_zic add_reduced
      (collecting_binary_forward Z.add).
Proof.
  move=> Hex. apply: quad_set_not_representable.
  exists (nb_car (add_reduced op08 op03)).
  have Hrep := Hex op08 op03.
  have Hgoal : γ[prod_ajsl] (nb_car (add_reduced op08 op03)) ⊆⊇ quad_set.
  { transitivity (collecting_binary_forward Z.add
                    (γ[non_bottom_zic] op08) (γ[non_bottom_zic] op03)).
    - exact: Hrep.
    - exact: add_collecting_quad. }
  exact: Hgoal.
Qed.

End AddNotExact.
