(* ZIntervalCongruence.v - Reduced product of integer intervals and
   integer congruences.

   The carrier is [interval * (Z * Z)] (an interval paired with a
   congruence (r, m) standing for r + mZ), and γ is the componentwise
   intersection.

   Two layers of structure:

   - [Conjunction.ajsl] over [itv] and [cong_ajsl] gives the carrier,
     the componentwise γ, the componentwise [⊑], and the componentwise
     join. We use the *plain* interval [itv] (not the [CollapsedBottom]
     variant [itv_canon]): a single [CollapsedBottom] on top of the
     whole conjunction is enough to make γ-empty pairs ⊑-minimal, so a
     second collapse on the interval component would be redundant.

   - [CollapsedBottom] on top of the conjunction widens [⊑] so that
     any γ-empty pair is below every element. This is what makes
     our chosen [bottom] a [⊑]-minimum: the per-component order on
     the conjunction is *not* enough, because the cong component
     [(0, 0)] (singleton {0}) is not ⊑-minimum in [cong_ajsl].

   The "reduced" part is a [Reduction] (in the sense of
   [Abstraction.v]) that propagates information across the two
   components. This file's strategy is to prove

       forall p, BestAbstraction (A := collapsed_ad) (reduce p) (γ[collapsed_ad] p)

   from which [Reduction] and [OptimalReduction] both follow via
   [best_abstraction_is_optimal_reduction] (the "α ∘ γ" recipe).

   STATUS: reduce: best abstraction — the maximal/optimal reduction,
   via the α∘γ recipe ([reduce_best_abstraction], [reduce_final_best]).
   Domains [zic] / [non_bottom_zic]: sound + JoinIsLUB.
   [is_singleton]: sound. *)

From Stdlib Require Import ZArith Lia.
Require Import ssreflect ssrbool.
Require Import base Abstraction AbstractLattice
  AbstractionCombination Z_interval Congruence.

Open Scope Z_scope.

(** Underlying unreduced join semilattice (componentwise everything),
    then with the order widened so γ-empty pairs are universal
    bottoms. *)
Definition prod_ajsl : abstract_join_semilattice Z :=
  Conjunction.ajsl itv cong_ajsl.

Instance prod_join_is_lub: JoinIsLUB prod_ajsl.
Proof.
  apply Conjunction.Conjunction_JoinIsLUB.
  apply _.
  apply _.
Qed.

Definition collapsed_ad : abstract_domain Z :=
  CollapsedBottom.ad prod_ajsl.

(** Canonical bottom. The interval component is γ-empty
    ([1 > 0]); the congruence component is [(0, 0)]. The conjunction
    is γ-empty regardless, so (via [CollapsedBottom]) it is [⊑] every
    element. *)
Definition bottom : collapsed_ad :=
  ((WithTop.NotTop 1, WithTop.NotTop 0), (0, 0)).

Lemma bottom_gamma_empty : γ[collapsed_ad] bottom ⊆⊇ ∅.
Proof.
  split=> c Hc; last by [].
  have [Hi _] := Hc.
  have [Hge Hle] : 1 <= c /\ c <= 0 by exact: Hi.
  lia.
Qed.

(** A γ-empty element is γ-equal to [bottom] (which is γ-empty), so
    [bottom] over-approximates it exactly. Packages the recurring
    "[transitivity ∅]" step in [reduce_preserves_gamma]. *)
Lemma bottom_gamma_of_empty (p : collapsed_ad) :
  γ[collapsed_ad] p ⊆⊇ ∅ -> γ[collapsed_ad] bottom ⊆⊇ γ[collapsed_ad] p.
Proof.
  move=> Hp. transitivity (∅ : propset Z); first exact: bottom_gamma_empty.
  by symmetry.
Qed.

(** Canonical bottom is MaximallyReduced: every value with the same
    (empty) concretization is above it. *)
Instance bottom_maximally_reduced :
  @MaximallyReduced Z collapsed_ad bottom.
Proof.
  apply: (CollapsedBottom.is_empty_maximally_reduced prod_ajsl).
  exact: bottom_gamma_empty.
Qed.

(** ** Bottom predicate.

    [is_bottom p] holds when the interval component's bounds are not
    well-ordered. This implies gamma-emptiness (empty interval forces
    the conjunction to be empty), but the converse only holds for
    elements satisfying [reduced_shape] (a non-empty interval paired
    with a disjoint congruence class can be gamma-empty without the
    interval being bottom). *)

Definition is_bottom (p : collapsed_ad) : Prop :=
  let '(i, _) := p in ~ non_bottom i.

Definition is_bottomb (p : collapsed_ad) : bool :=
  let '(i, _) := p in negb (non_bottomb i).

Lemma is_bottombP p : reflect (is_bottom p) (is_bottomb p).
Proof.
  case: p => i c.
  rewrite /is_bottom /is_bottomb /=.
  exact: negPP (non_bottombP i).
Qed.

Lemma is_bottom_bottom : is_bottom bottom.
Proof.
  rewrite /is_bottom /bottom /non_bottom /=. lia.
Qed.
  
Lemma is_bottom_gamma_empty p :
  is_bottom p -> γ[collapsed_ad] p ⊆⊇ ∅.
Proof.
  case: p => i c.
  rewrite /is_bottom /= => Hnot_nb.
  split=> z Hz; last by [].
  have [Hzi _] := Hz.
  have /non_bottom_non_empty Hnb : exists w, w ∈ γ[itv] i by exists z.
  exact: Hnot_nb Hnb.
Qed.

(** ** Snap helpers.

    For [m' > 0], the smallest [k ≥ lz] with [k ≡ r (mod m')] is
    [lz + (r - lz) mod m']; the largest [k ≤ hz] with [k ≡ r (mod m')]
    is [hz - (hz - r) mod m']. *)

Definition snap_low_z (lz r m' : Z) : Z := lz + (r - lz) mod m'.
Definition snap_high_z (hz r m' : Z) : Z := hz - (hz - r) mod m'.

Lemma snap_low_z_ge lz r m' : 0 < m' -> lz <= snap_low_z lz r m'.
Proof.
  move=> Hm. rewrite /snap_low_z.
  have Hb := Z.mod_pos_bound (r - lz) m' Hm.
  lia.
Qed.

Lemma snap_high_z_le hz r m' : 0 < m' -> snap_high_z hz r m' <= hz.
Proof.
  move=> Hm. rewrite /snap_high_z.
  have Hb := Z.mod_pos_bound (hz - r) m' Hm.
  lia.
Qed.

Lemma snap_low_z_cong lz r m' : 0 < m' -> (m' | snap_low_z lz r m' - r).
Proof.
  move=> Hm. rewrite /snap_low_z.
  have Heq := Z.mod_eq (r - lz) m' (not_eq_sym (Z.lt_neq _ _ Hm)).
  exists (- ((r - lz) / m')). lia.
Qed.

Lemma snap_high_z_cong hz r m' : 0 < m' -> (m' | snap_high_z hz r m' - r).
Proof.
  move=> Hm. rewrite /snap_high_z.
  have Heq := Z.mod_eq (hz - r) m' (not_eq_sym (Z.lt_neq _ _ Hm)).
  exists ((hz - r) / m'). lia.
Qed.

Lemma snap_low_z_smallest lz r m' z :
  0 < m' -> lz <= z -> (m' | z - r) -> snap_low_z lz r m' <= z.
Proof.
  move=> Hm Hge [k Hk].
  rewrite /snap_low_z.
  have Hb := Z.mod_pos_bound (r - lz) m' Hm.
  have Heq := Z.mod_eq (r - lz) m' (not_eq_sym (Z.lt_neq _ _ Hm)).
  set q := (r - lz) / m' in Heq.
  set rmod := (r - lz) mod m' in Hb Heq.
  have Hzlz : z - lz = (q + k) * m' + rmod by lia.
  have Hqk_nn : 0 <= q + k by nia.
  nia.
Qed.

Lemma snap_high_z_largest hz r m' z :
  0 < m' -> z <= hz -> (m' | z - r) -> z <= snap_high_z hz r m' .
Proof.
  move=> Hm Hle [k Hk].
  rewrite /snap_high_z.
  have Hb := Z.mod_pos_bound (hz - r) m' Hm.
  have Heq := Z.mod_eq (hz - r) m' (not_eq_sym (Z.lt_neq _ _ Hm)).
  set q := (hz - r) / m' in Heq.
  set rmod := (hz - r) mod m' in Hb Heq.
  have Hzhz : hz - z = (q - k) * m' + rmod by lia.
  have Hqk_nn : 0 <= q - k by nia.
  nia.
Qed.

(** ** WithTop-lifted snap. *)

Definition snap_low (l : WithTop.with_top Z) (r m' : Z) : WithTop.with_top Z :=
  match l with
  | WithTop.Top => WithTop.Top
  | WithTop.NotTop lz => WithTop.NotTop (snap_low_z lz r m')
  end.

Definition snap_high (h : WithTop.with_top Z) (r m' : Z) : WithTop.with_top Z :=
  match h with
  | WithTop.Top => WithTop.Top
  | WithTop.NotTop hz => WithTop.NotTop (snap_high_z hz r m')
  end.

(** ** Reduction.

    Given a non-bottom interval [(l, h)] and a congruence [(r, m)]:
    - if [m = 0], the cong is the singleton [{r}]; produce the
      singleton interval (or bottom if [r ∉ [l, h]]);
    - otherwise, snap each finite endpoint to the nearest element of
      [r + |m|Z], then return either bottom (if the snapped interval
      is empty), the singleton (if it collapsed to one point), or
      the snapped pair otherwise. *)

(** Build a non-empty result from snapped bounds. If both are
    [NotTop] and equal, lift the singleton into the congruence. *)
Definition build_snapped (l h : WithTop.with_top Z) (r m' : Z) : collapsed_ad :=
  match l, h with
  | WithTop.NotTop lz, WithTop.NotTop hz =>
      if Z.ltb hz lz then bottom
      else if Z.eqb lz hz
        then ((l, h), (lz, 0))
        else ((l, h), (r, m'))
  | _, _ => ((l, h), (r, m'))
  end.

Definition reduce (p : collapsed_ad) : collapsed_ad :=
  let (i, c) := p in
  let (r, m) := c in
  if non_bottomb i then
    let l := fst i in
    let h := snd i in
    if Z.eqb m 0 then
      if itv_gammab (l, h) r then
        ((WithTop.NotTop r, WithTop.NotTop r), (r, 0))
      else bottom
    else
      let m' := Z.abs m in
      build_snapped (snap_low l r m') (snap_high h r m') r m'
  else bottom.

(** ** Main proof obligation.

    Goal: prove that [reduce] is the maximal reduction by showing
    that, for every input [p], [reduce p] is a [BestAbstraction] of
    [γ[collapsed_ad] p]. *)

(** ** Singleton output helpers. *)

Lemma singleton_le_itv (z : Z) (i : interval) :
  z ∈ γ[itv] i -> (WithTop.NotTop z, WithTop.NotTop z) ⊑[itv] i.
Proof.
  case: i => l h Hin.
  apply/is_includedP. move/itv_gammaP: Hin.
  by case: l; case: h.
Qed.

Lemma singleton_gamma_eq (z : Z) :
  γ[collapsed_ad] ((WithTop.NotTop z, WithTop.NotTop z), (z, 0)) ⊆⊇
  {[ x | x = z ]}.
Proof.
  apply propset_equiv_iff => x. split.
  - move=> [Hxi Hxc].
    move/gamma_singleton: Hxc => ->.
    by apply/propset_elem_of_iff.
  - move/propset_elem_of_iff => ->.
    split.
    + simpl. unfold_set. simpl. lia.
    + by apply/gamma_singleton.
Qed.

(** When [r ∈ γ_itv i] and [m = 0], the conjunction γ collapses to
    [{r}]: γ_cong (r, 0) = {r} and γ_itv ∩ {r} = {r}. *)
Lemma gamma_pair_singleton_hit (i : interval) (r : Z) :
  r ∈ γ[itv] i ->
  γ[collapsed_ad] (i, (r, 0)) ⊆⊇ {[ x | x = r ]}.
Proof.
  move=> Hin. apply propset_equiv_iff => x. split.
  - move=> [_ Hxc]. apply/propset_elem_of_iff. by apply/gamma_singleton.
  - move/propset_elem_of_iff => ->. split.
    + exact: Hin.
    + by apply/gamma_singleton.
Qed.

(** *** Singleton output is MaximallyReduced.

    For the singleton output [((WithTop.NotTopz, NotTop z), (z, 0))], the
    interval side is the unique tightest interval containing [z], and
    the cong side [(z, 0)] is the unique tightest cong representing
    [{z}]. Both components are [⊑]-minimum among over-approximations
    of [{z}]. *)
Lemma singleton_maximally_reduced (z : Z) :
  MaximallyReduced (A := collapsed_ad)
    ((WithTop.NotTop z, WithTop.NotTop z), (z, 0)).
Proof.
  unfold MaximallyReduced. split.
  - by [].
  - move=> [ai ac] Ha.
    have Hz_in_a : z ∈ γ[collapsed_ad] ((WithTop.NotTop z, WithTop.NotTop z), (z, 0)).
    { split.
      + simpl. unfold_set. simpl. lia.
      + by apply/gamma_singleton. }
    have [Hzi Hzc] := Ha _ Hz_in_a.
    right. split.
    + (* itv side: ⊑[itv] directly (no inner collapse). *)
      apply: singleton_le_itv. exact: Hzi.
    + case: ac Hzc {Ha Hz_in_a} => rb mb Hzc.
      apply (proj2 (singleton_order_gamma z rb mb)). exact: Hzc.
Qed.

(** ** Helpers for γ-emptiness in the input. *)

(** When the underlying interval is not [non_bottom], the conjunction
    is γ-empty. *)
Lemma gamma_pair_empty_of_non_bottomb (i : interval) (c : Z * Z) :
  non_bottomb i = false -> γ[collapsed_ad] (i, c) ⊆⊇ ∅.
Proof.
  move=> Hnb. split=> z Hz; last by [].
  have [Hzi _] := Hz.
  have Hne : exists w, w ∈ γ[itv] i by exists z.
  move/non_bottom_non_empty: Hne => /non_bottombP.
  by rewrite Hnb.
Qed.

(** When [m = 0] and [r ∉ γ_itv i], the conjunction is γ-empty. *)
Lemma gamma_pair_empty_of_singleton_miss (i : interval) (r : Z) :
  ~ (r ∈ γ[itv] i) -> γ[collapsed_ad] (i, (r, 0)) ⊆⊇ ∅.
Proof.
  move=> Hmiss. split=> z Hz; last by [].
  have [Hzi Hzc] := Hz.
  apply: Hmiss.
  have Hzr : z = r by apply/gamma_singleton.
  by rewrite -Hzr.
Qed.

(** Per-component "snap preserves γ on the cong-class slice". *)
Lemma gamma_glbtop_snap_low_iff (l : WithTop.with_top Z) (r m' x : Z) :
  0 < m' -> (m' | x - r) ->
  x ∈ γ[glbtop] (snap_low l r m') <-> x ∈ γ[glbtop] l.
Proof.
  move=> Hm Hd. case: l => [|lz] //=.
  rewrite /snap_low. split=> Hge.
  - have Hlb := snap_low_z_ge lz r m' Hm.
    have Hge' : snap_low_z lz r m' <= x by exact: Hge.
    apply propset_elem_of_iff. lia.
  - apply: snap_low_z_smallest => //.
Qed.

Lemma gamma_lubtop_snap_high_iff (h : WithTop.with_top Z) (r m' x : Z) :
  0 < m' -> (m' | x - r) ->
  x ∈ γ[lubtop] (snap_high h r m') <-> x ∈ γ[lubtop] h.
Proof.
  move=> Hm Hd. case: h => [|hz] //=.
  rewrite /snap_high. split=> Hle.
  - have Hub := snap_high_z_le hz r m' Hm.
    have Hle' : x <= snap_high_z hz r m' by exact: Hle.
    apply propset_elem_of_iff. lia.
  - apply: snap_high_z_largest => //.
Qed.

(** Build_snapped output γ-equals γ p on the four non-bottom branches. *)
Lemma gamma_pair_build_snapped_eq
  (i : interval) (r m : Z) (l' h' : WithTop.with_top Z) :
  m <> 0 ->
  snap_low (fst i) r (Z.abs m) = l' ->
  snap_high (snd i) r (Z.abs m) = h' ->
  γ[collapsed_ad] ((l', h'), (r, Z.abs m)) ⊆⊇ γ[collapsed_ad] (i, (r, m)).
Proof.
  move=> Hm Esl Esh.
  have Hm' : 0 < Z.abs m by lia.
  apply propset_equiv_iff => x. split.
  - move=> [Hxi Hxc].
    have Hxc_a : (Z.abs m | x - r) by exact Hxc.
    have Hxc_m : (m | x - r) by apply/Z.divide_abs_l; exact Hxc_a.
    have [Hxg Hxlu] : x ∈ γ[glbtop] l' /\ x ∈ γ[lubtop] h'.
    { case: Hxi => ? ?. by split. }
    split; last exact Hxc_m.
    rewrite -Esl in Hxg. rewrite -Esh in Hxlu.
    move/(gamma_glbtop_snap_low_iff _ _ _ _ Hm' Hxc_a): Hxg => Hxg.
    move/(gamma_lubtop_snap_high_iff _ _ _ _ Hm' Hxc_a): Hxlu => Hxlu.
    case: i Esl Esh Hxg Hxlu {Hxi Hxc} => ll hh /=.
    by move=> _ _ ? ?; split.
  - move=> [Hxi Hxc].
    have Hxc_a : (Z.abs m | x - r) by apply/Z.divide_abs_l; exact Hxc.
    have [Hxg_orig Hxlu_orig] : x ∈ γ[glbtop] (fst i) /\
                                x ∈ γ[lubtop] (snd i).
    { case: i Hxi {Esl Esh} => ll hh /= [? ?]. by split. }
    split; last exact Hxc_a.
    rewrite -Esl -Esh.
    move/(gamma_glbtop_snap_low_iff _ _ _ _ Hm' Hxc_a): Hxg_orig => Hxg_snap.
    move/(gamma_lubtop_snap_high_iff _ _ _ _ Hm' Hxc_a): Hxlu_orig => Hxlu_snap.
    by split.
Qed.

(** When [m ≠ 0] and the snapped bounds collapse to the same value
    [l'z], the conjunction γ collapses to [{l'z}]. *)
Lemma gamma_pair_snap_collapse
  (i : interval) (r m l'z : Z) :
  m <> 0 ->
  snap_low (fst i) r (Z.abs m) = WithTop.NotTop l'z ->
  snap_high (snd i) r (Z.abs m) = WithTop.NotTop l'z ->
  γ[collapsed_ad] (i, (r, m)) ⊆⊇ {[ x | x = l'z ]}.
Proof.
  move=> Hm Esl Esh.
  have Hm' : 0 < Z.abs m by lia.
  case: i Esl Esh => ll hh /= Esl Esh.
  case: ll Esl => [|lz] // Esl.
  case: hh Esh => [|hz] // Esh.
  rewrite /snap_low in Esl. case: Esl => Elz.
  rewrite /snap_high in Esh. case: Esh => Ehz.
  have Hge_lz : lz <= l'z by rewrite -Elz; apply: snap_low_z_ge.
  have Hle_hz : l'z <= hz by rewrite -Ehz; apply: snap_high_z_le.
  have Hdiv_l'z : (m | l'z - r).
  { apply/Z.divide_abs_l. rewrite -Elz. exact: snap_low_z_cong. }
  apply propset_equiv_iff => x. split.
  - move=> [Hxi Hxc].
    have [Hge Hle] : lz <= x /\ x <= hz by exact: Hxi.
    have Hdiv : (Z.abs m | x - r) by apply/Z.divide_abs_l; exact Hxc.
    have Hl := snap_low_z_smallest lz r (Z.abs m) x Hm' Hge Hdiv.
    have Hh := snap_high_z_largest hz r (Z.abs m) x Hm' Hle Hdiv.
    apply/propset_elem_of_iff. lia.
  - move/propset_elem_of_iff => ->. split.
    + simpl. unfold_set. simpl. lia.
    + simpl. by [].
Qed.

(** When [m ≠ 0] and the snapped bounds cross (h'z < l'z), no element
    of the original interval can be congruent to [r] modulo [|m|]. *)
Lemma gamma_pair_empty_of_snap_disjoint
  (i : interval) (r m l'z h'z : Z) :
  m <> 0 ->
  snap_low (fst i) r (Z.abs m) = WithTop.NotTop l'z ->
  snap_high (snd i) r (Z.abs m) = WithTop.NotTop h'z ->
  h'z < l'z ->
  γ[collapsed_ad] (i, (r, m)) ⊆⊇ ∅.
Proof.
  move=> Hm Esl Esh Hlt.
  have Hm' : 0 < Z.abs m by lia.
  case: i Esl Esh => ll hh /= Esl Esh.
  case: ll Esl => [|lz] // Esl.
  case: hh Esh => [|hz] // Esh.
  rewrite /snap_low in Esl. case: Esl => Elz.
  rewrite /snap_high in Esh. case: Esh => Ehz.
  split=> z Hz; last by [].
  exfalso.
  have [Hzi Hzc] := Hz. clear Hz.
  have [Hge Hle] : lz <= z /\ z <= hz by exact: Hzi.
  have Hdiv : (Z.abs m | z - r) by apply/Z.divide_abs_l; exact Hzc.
  have Hl := snap_low_z_smallest lz r (Z.abs m) z Hm' Hge Hdiv.
  have Hh := snap_high_z_largest hz r (Z.abs m) z Hm' Hle Hdiv.
  lia.
Qed.

(** ** Main proof, split into γ-preservation and MaximallyReduced. *)

(** *** γ-preservation. *)
Lemma reduce_preserves_gamma (p : collapsed_ad) :
  γ[collapsed_ad] (reduce p) ⊆⊇ γ[collapsed_ad] p.
Proof.
  case: p => i [r m].
  rewrite /reduce.
  case_eq (non_bottomb i) => Hnb.
  - case_eq (Z.eqb m 0) => Hm0.
    + case_eq (itv_gammab (fst i, snd i) r) => Hmem.
      * (* B2: singleton {r} in [l,h]. *)
        move/Z.eqb_eq: Hm0 => ?; subst m.
        have Hin : r ∈ γ[itv] (fst i, snd i)
          by apply/itv_gammaP; rewrite Hmem.
        clear Hmem.
        have Hin' : r ∈ γ[itv] i by case: i Hnb Hin => [ii1 ii2] _ /=.
        clear Hin.
        transitivity ({[ x | x = r ]} : propset Z).
        -- exact: singleton_gamma_eq.
        -- symmetry. exact: gamma_pair_singleton_hit.
      * (* B3: γ p = ∅, γ bottom = ∅. *)
        move/Z.eqb_eq: Hm0 => ?; subst m.
        have Hmem' : ~ r ∈ γ[itv] (fst i, snd i) by apply/itv_gammaP; rewrite Hmem.
        clear Hmem.
        have Hgp : γ[collapsed_ad] (i, (r, 0)) ⊆⊇ ∅.
        { apply: gamma_pair_empty_of_singleton_miss.
          case: i Hnb Hmem' => [ii1 ii2] _ /= Hmem' Hin.
          exact: Hmem' Hin. }
        exact: bottom_gamma_of_empty Hgp.
    + set m' := Z.abs m.
      move/Z.eqb_neq: Hm0 => Hmne.
      rewrite /build_snapped.
      case_eq (snap_low (fst i) r m') => [|l'z] El';
      case_eq (snap_high (snd i) r m') => [|h'z] Eh';
        (* B4d-1/2/3: at least one [Top] bound; [build_snapped] returns
           the snapped pair directly. *)
        try exact: gamma_pair_build_snapped_eq i r m _ _ Hmne El' Eh'.
      (* Both bounds finite: split on the snapped range. *)
      case_eq (Z.ltb h'z l'z) => Hlt.
      * (* B4a: snapped bounds cross — empty. *)
        move/Z.ltb_lt: Hlt => Hlt'.
        have Hgp := gamma_pair_empty_of_snap_disjoint
                      i r m l'z h'z Hmne El' Eh' Hlt'.
        exact: bottom_gamma_of_empty Hgp.
      * case_eq (Z.eqb l'z h'z) => Heq.
        -- (* B4b: snap collapses to {l'z}. *)
           move/Z.eqb_eq: Heq => ?; subst h'z.
           transitivity ({[ x | x = l'z ]} : propset Z).
           ++ exact: singleton_gamma_eq.
           ++ symmetry. exact: gamma_pair_snap_collapse i r m l'z Hmne El' Eh'.
        -- (* B4c: snapped range *)
           exact: gamma_pair_build_snapped_eq i r m _ _ Hmne El' Eh'.
  - (* B1: γ p = ∅, γ bottom = ∅. *)
    have Hgp := gamma_pair_empty_of_non_bottomb i (r, m) Hnb.
    exact: bottom_gamma_of_empty Hgp.
Qed.

(** ** Witness / unboundedness helpers for the snapped output's γ. *)

(** When [snap_low (fst (` i)) r m' = Top], the original lower bound
    is [Top], so [γ_output] is unbounded below in the cong class. *)
Lemma snap_low_Top_inv (l : WithTop.with_top Z) (r m' : Z) :
  snap_low l r m' = WithTop.Top -> l = WithTop.Top.
Proof. rewrite /snap_low. by case: l. Qed.

Lemma snap_high_Top_inv (h : WithTop.with_top Z) (r m' : Z) :
  snap_high h r m' = WithTop.Top -> h = WithTop.Top.
Proof. rewrite /snap_high. by case: h. Qed.

(** [r] is in [γ_output] when [m ≠ 0] and the interval covers it.
    For B4d-* / B4c branches we'll often use a different witness. *)

(** AP-element witness via cong: [r + k*m'] is in [γ_cong (r, m')]. *)
Lemma cong_AP_pt (r m' k : Z) : r + k * m' ∈ γ[cong_ajsl] (r, m').
Proof. simpl. unfold_set. exists k. lia. Qed.

(** Two-points lemma: any cong [ac] containing two AP points differing
    by exactly [m'] (with [m' > 0]) covers the entire AP at [(r, m')]. *)
Lemma cong_le_via_two_pts (r m' : Z) (ac : Z * Z) (x : Z) :
  0 < m' ->
  (m' | x - r) ->
  x ∈ γ[cong_ajsl] ac ->
  (x + m') ∈ γ[cong_ajsl] ac ->
  (r, m') ⊑[cong_ajsl] ac.
Proof.
  move=> Hm' Hxr Hx Hxm.
  apply: (proj2 (cong_exact_order _ _)).
  move=> z Hz.
  have Hzr : (m' | z - r) by exact: Hz.
  case: ac Hx Hxm => [ra ma] /=. unfold_set => [[k1 Hk1]] [k2 Hk2].
  have Hma_m' : (ma | m').
  { exists (k2 - k1). lia. }
  have Hxma : (ma | x - ra) by exists k1; lia.
  have Hzma : (ma | z - x).
  { case: Hxr => [j1 Hj1]. case: Hzr => [j2 Hj2].
    case: Hma_m' => [u Hu]. exists ((j2 - j1) * u). nia. }
  have : (ma | z - ra).
  { replace (z - ra) with ((z - x) + (x - ra)) by lia.
    apply: Z.divide_add_r; assumption. }
  case=> j Hj. exists j; lia.
Qed.

(** AP unboundedness: for any [a], there's an AP point below [a]. *)
Lemma cong_unbounded_below (r m' a : Z) :
  0 < m' -> exists z, z ∈ γ[cong_ajsl] (r, m') /\ z < a.
Proof.
  move=> Hm'.
  set k := Z.abs (a - r) + 1.
  have Hk1 : 1 <= k by lia.
  exists (r - k * m'). split.
  - simpl. unfold_set. by exists (- k); lia.
  - have Hkm : k <= k * m' by nia.
    have Hra : r - a <= Z.abs (a - r) by lia.
    lia.
Qed.

Lemma cong_unbounded_above (r m' a : Z) :
  0 < m' -> exists z, z ∈ γ[cong_ajsl] (r, m') /\ a < z.
Proof.
  move=> Hm'.
  set k := Z.abs (a - r) + 1.
  have Hk1 : 1 <= k by lia.
  exists (r + k * m'). split.
  - simpl. unfold_set. by exists k; lia.
  - have Hkm : k <= k * m' by nia.
    have Hra : a - r <= Z.abs (a - r) by lia.
    lia.
Qed.

(** Bridges from γ-membership to ⊑ in the bound domains. *)
Lemma gamma_lubtop_le (c : Z) (b : WithTop.with_top Z) :
  c ∈ γ[lubtop] b -> WithTop.NotTop c ⊑[lubtop] b.
Proof. by case: b => [|hh] /=. Qed.

Lemma gamma_glbtop_le (c : Z) (b : WithTop.with_top Z) :
  c ∈ γ[glbtop] b -> WithTop.NotTop c ⊑[glbtop] b.
Proof. by case: b => [|lz] /=. Qed.

(** ** Structural shape of [reduce]'s output.

    We characterise the possible outputs of [reduce] with an inductive
    predicate [reduced_shape], and prove [MaximallyReduced] once for
    every value satisfying that predicate. The proof of
    [reduce_maximally_reduced] then splits cleanly into a structural
    part ([reduce_reduced_shape], pure case analysis on [reduce]'s
    definition) and an analytical part
    ([reduced_shape_maximally_reduced], the Galois-style content). *)

(** A bound is "ok" relative to a congruence [(r, m)] if it is either
    [Top] or it lies on the AP {r + k*m}. *)
Definition cong_bound_ok (r m : Z) (b : WithTop.with_top Z) : Prop :=
  match b with
  | WithTop.Top      => True
  | WithTop.NotTop z => (m | z - r)
  end.

(** Strict ordering on [with_top Z], with [Top] as +∞ on the right and
    -∞ on the left. Any pair involving a [Top] is "strict". *)
Definition lt_with_top (l h : WithTop.with_top Z) : Prop :=
  match l, h with
  | WithTop.NotTop lz, WithTop.NotTop hz => lz < hz
  | _, _ => True
  end.

Inductive reduced_shape : collapsed_ad -> Prop :=
| RS_bottom : forall p, is_bottom p -> reduced_shape p
| RS_singleton : forall r : Z,
    reduced_shape
      ((WithTop.NotTop r, WithTop.NotTop r), (r, 0))
| RS_interval : forall (l h : WithTop.with_top Z) (r m : Z),
    0 < m ->
    cong_bound_ok r m l ->
    cong_bound_ok r m h ->
    lt_with_top l h ->
    reduced_shape ((l, h), (r, m)).

(** When the bounds of an interval are both cong-class elements with
    [l'z < h'z], they differ by at least [m]. *)
Lemma cong_gap_ge (r m l'z h'z : Z) :
  0 < m -> (m | l'z - r) -> (m | h'z - r) -> l'z < h'z ->
  l'z + m <= h'z.
Proof.
  move=> Hm [k1 Hk1] [k2 Hk2] Hlt.
  have Hd : h'z - l'z = (k2 - k1) * m by lia.
  have Hpos : 0 < (k2 - k1) * m by lia.
  have Hkk : 1 <= k2 - k1 by nia.
  nia.
Qed.

(** Membership lemmas: witnesses for the [MaximallyReduced]
    proof of an [RS_interval] value. *)

Lemma RS_interval_l'z_in (h : WithTop.with_top Z) (r m l'z : Z) :
  0 < m ->
  cong_bound_ok r m h ->
  lt_with_top (WithTop.NotTop l'z) h ->
  (m | l'z - r) ->
  l'z ∈ γ[collapsed_ad] ((WithTop.NotTop l'z, h), (r, m)).
Proof.
  move=> Hm Hh Hlh Hcong. case: h Hh Hlh => [|hz] Hh Hlh.
  - split.
    + simpl. unfold_set. simpl. lia.
    + simpl. unfold_set. by case: Hcong => k Hk; exists k; lia.
  - split.
    + simpl. unfold_set. simpl. simpl in Hlh. lia.
    + simpl. unfold_set. by case: Hcong => k Hk; exists k; lia.
Qed.

Lemma RS_interval_l'zm_in (h : WithTop.with_top Z) (r m l'z : Z) :
  0 < m ->
  cong_bound_ok r m h ->
  lt_with_top (WithTop.NotTop l'z) h ->
  (m | l'z - r) ->
  (l'z + m) ∈ γ[collapsed_ad] ((WithTop.NotTop l'z, h), (r, m)).
Proof.
  move=> Hm Hh Hlh Hcong. case: h Hh Hlh => [|hz] Hh Hlh.
  - split.
    + simpl. unfold_set. simpl. lia.
    + simpl. unfold_set. case: Hcong => k Hk. exists (k + 1); lia.
  - split.
    + simpl. unfold_set. simpl.
      simpl in Hh, Hlh.
      have Hge := cong_gap_ge r m l'z hz Hm Hcong Hh Hlh. lia.
    + simpl. unfold_set. case: Hcong => k Hk. exists (k + 1); lia.
Qed.

Lemma RS_interval_h'z_in (l : WithTop.with_top Z) (r m h'z : Z) :
  0 < m ->
  cong_bound_ok r m l ->
  lt_with_top l (WithTop.NotTop h'z) ->
  (m | h'z - r) ->
  h'z ∈ γ[collapsed_ad] ((l, WithTop.NotTop h'z), (r, m)).
Proof.
  move=> Hm Hl Hlh Hcong. case: l Hl Hlh => [|lz] Hl Hlh.
  - split.
    + simpl. unfold_set. simpl. lia.
    + simpl. unfold_set. by case: Hcong => k Hk; exists k; lia.
  - split.
    + simpl. unfold_set. simpl. simpl in Hlh. lia.
    + simpl. unfold_set. by case: Hcong => k Hk; exists k; lia.
Qed.

Lemma RS_interval_h'zm_in (l : WithTop.with_top Z) (r m h'z : Z) :
  0 < m ->
  cong_bound_ok r m l ->
  lt_with_top l (WithTop.NotTop h'z) ->
  (m | h'z - r) ->
  (h'z - m) ∈ γ[collapsed_ad] ((l, WithTop.NotTop h'z), (r, m)).
Proof.
  move=> Hm Hl Hlh Hcong. case: l Hl Hlh => [|lz] Hl Hlh.
  - split.
    + simpl. unfold_set. simpl. lia.
    + simpl. unfold_set. case: Hcong => k Hk. exists (k - 1); lia.
  - split.
    + simpl. unfold_set. simpl.
      simpl in Hl, Hlh.
      have Hge := cong_gap_ge r m lz h'z Hm Hl Hcong Hlh. lia.
    + simpl. unfold_set. case: Hcong => k Hk. exists (k - 1); lia.
Qed.

(** *** Witness pair for the cong side: we always find two AP-consecutive
    points in [γ a]. This is the reusable lemma the [(r, m)] best-cong
    proof needs. *)
Lemma RS_interval_witness l h r m :
  0 < m ->
  cong_bound_ok r m l ->
  cong_bound_ok r m h ->
  lt_with_top l h ->
  exists x : Z, (m | x - r) /\
    x ∈ γ[collapsed_ad] ((l, h), (r, m)) /\
    (x + m) ∈ γ[collapsed_ad] ((l, h), (r, m)).
Proof.
  move=> Hm Hl Hh Hlh.
  case: l Hl Hlh => [|l'z] Hl Hlh; last first.
  { simpl in Hl.
    exists l'z; split; first exact Hl.
    case: h Hh Hlh => [|h'z] Hh Hlh.
    - split.
      + exact: (RS_interval_l'z_in WithTop.Top r m l'z Hm I I Hl).
      + exact: (RS_interval_l'zm_in WithTop.Top r m l'z Hm I I Hl).
    - simpl in Hh, Hlh. split.
      + exact: (RS_interval_l'z_in (WithTop.NotTop h'z) r m l'z Hm Hh Hlh Hl).
      + exact: (RS_interval_l'zm_in (WithTop.NotTop h'z) r m l'z Hm Hh Hlh Hl). }
  case: h Hh Hlh => [|h'z] Hh Hlh.
  - (* Top, Top: x = r *)
    exists r; split; first by exists 0; lia.
    split; split.
    + simpl. unfold_set. by [].
    + simpl. unfold_set. by exists 0; lia.
    + simpl. unfold_set. by [].
    + simpl. unfold_set. by exists 1; lia.
  - (* Top, NotTop h'z: x = h'z - m *)
    simpl in Hh.
    exists (h'z - m). split.
    { case: Hh => k Hk. exists (k - 1); lia. }
    split.
    + exact: (RS_interval_h'zm_in WithTop.Top r m h'z Hm I I Hh).
    + have ->: h'z - m + m = h'z by lia.
      exact: (RS_interval_h'z_in WithTop.Top r m h'z Hm I I Hh).
Qed.

(* When [p] satisfies [reduced_shape], we can check that the
   concretization is empty by looking only at the interval. *)
Lemma gamma_empty_is_bottom p :
  reduced_shape p -> γ[collapsed_ad] p ⊆⊇ ∅ -> is_bottom p.
Proof.
  case=> {p}.
  - move=> p Hbot _. exact: Hbot.
  - move=> r Hempty.
    have : r ∈ γ[collapsed_ad] ((WithTop.NotTop r, WithTop.NotTop r), (r, 0)).
    { split.
      - apply/itv_gammaP.
        rewrite /itv_gammab /=. apply/andP; split; apply/Z.leb_spec0; lia.
      - rewrite gamma_singleton. reflexivity. }
    move=> /(proj1 Hempty) //.
  - move=> l h r m Hm Hl Hh Hlh Hempty.
    have Hwit := RS_interval_witness l h r m Hm Hl Hh Hlh.
    move: Hwit => [x [Hdiv [Hxg _]]].
    exfalso. exact: (proj1 Hempty x Hxg).
Qed.

(** *** Forcing lemmas for the itv side. Centralise the case analysis
    on whether each bound is [Top] or finite. *)

Lemma RS_interval_glbtop_le l h r m ai ac :
  0 < m -> cong_bound_ok r m l -> cong_bound_ok r m h -> lt_with_top l h ->
  Overapproximates (A := collapsed_ad) (ai, ac)
    (γ[collapsed_ad] ((l, h), (r, m))) ->
  l ⊑[glbtop] (fst ai).
Proof.
  move=> Hm Hl Hh Hlh Ha.
  case: l Hl Hlh Ha => [|l'z] Hl Hlh Ha; last first.
  { simpl in Hl.
    have Hl'z_in : l'z ∈ γ[collapsed_ad]
      ((WithTop.NotTop l'z, h), (r, m))
      := RS_interval_l'z_in h r m l'z Hm Hh Hlh Hl.
    have [Hl'zi _] := Ha _ Hl'z_in.
    case Eai : ai => [la ha].
    rewrite Eai /= in Hl'zi.
    case: Hl'zi => Hge _. by apply: gamma_glbtop_le. }
  (* l = Top: force fst ai = Top *)
  case Eai : ai => [la ha] /=.
  case: la Eai => // za Eai. exfalso.
  have [z [Hz_in Hzlt]] :
    exists z, z ∈ γ[collapsed_ad] ((WithTop.Top, h), (r, m)) /\ z < za.
  { case: h Hh Hlh Ha => [|hz] Hh Hlh Ha.
    - have [z [Hz Hlt]] := cong_unbounded_below r m za Hm.
      exists z. split; last exact Hlt.
      split; first by simpl; unfold_set.
      exact Hz.
    - simpl in Hh.
      have [z [Hz Hlt]] := cong_unbounded_below r m (Z.min za (hz - 1)) Hm.
      exists z. split; last by lia.
      split; last exact Hz.
      simpl. unfold_set. simpl. lia. }
  have [Hzi _] := Ha _ Hz_in.
  rewrite Eai in Hzi. case: Hzi => Hge _.
  have Hge_z : za <= z by exact Hge. lia.
Qed.

Lemma RS_interval_lubtop_le l h r m ai ac :
  0 < m -> cong_bound_ok r m l -> cong_bound_ok r m h -> lt_with_top l h ->
  Overapproximates (A := collapsed_ad) (ai, ac)
    (γ[collapsed_ad] ((l, h), (r, m))) ->
  h ⊑[lubtop] (snd ai).
Proof.
  move=> Hm Hl Hh Hlh Ha.
  case: h Hh Hlh Ha => [|h'z] Hh Hlh Ha; last first.
  { simpl in Hh.
    have Hh'z_in : h'z ∈ γ[collapsed_ad]
      ((l, WithTop.NotTop h'z), (r, m))
      := RS_interval_h'z_in l r m h'z Hm Hl Hlh Hh.
    have [Hh'zi _] := Ha _ Hh'z_in.
    case Eai : ai => [la ha].
    rewrite Eai /= in Hh'zi.
    case: Hh'zi => _ Hle. by apply: gamma_lubtop_le. }
  (* h = Top: force snd ai = Top *)
  case Eai : ai => [la ha] /=.
  case: ha Eai => // za Eai. exfalso.
  have [z [Hz_in Hzgt]] :
    exists z, z ∈ γ[collapsed_ad] ((l, WithTop.Top), (r, m)) /\ za < z.
  { case: l Hl Hlh Ha => [|lz] Hl Hlh Ha.
    - have [z [Hz Hgt]] := cong_unbounded_above r m za Hm.
      exists z. split; last exact Hgt.
      split; first by simpl; unfold_set.
      exact Hz.
    - simpl in Hl.
      have [z [Hz Hgt]] := cong_unbounded_above r m (Z.max za (lz + 1)) Hm.
      exists z. split; last by lia.
      split; last exact Hz.
      simpl. unfold_set. simpl. lia. }
  have [Hzi _] := Ha _ Hz_in.
  rewrite Eai in Hzi. case: Hzi => _ Hle.
  have Hle_z : z <= za by exact Hle. lia.
Qed.

(** *** RS_interval values are MaximallyReduced. *)
Lemma RS_interval_maximally_reduced l h r m :
  0 < m -> cong_bound_ok r m l -> cong_bound_ok r m h -> lt_with_top l h ->
  MaximallyReduced (A := collapsed_ad) ((l, h), (r, m)).
Proof.
  move=> Hm Hl Hh Hlh.
  unfold MaximallyReduced. split; first by [].
  move=> [ai ac] Ha.
  have Hl_le := RS_interval_glbtop_le l h r m ai ac Hm Hl Hh Hlh Ha.
  have Hh_le := RS_interval_lubtop_le l h r m ai ac Hm Hl Hh Hlh Ha.
  have [x [Hxr [HxS HxmS]]] := RS_interval_witness l h r m Hm Hl Hh Hlh.
  have [_ Hxc] := Ha _ HxS.
  have [_ Hxmc] := Ha _ HxmS.
  have Hcong_le : (r, m) ⊑[cong_ajsl] ac
    := cong_le_via_two_pts r m ac x Hm Hxr Hxc Hxmc.
  right. split; last exact Hcong_le.
  (* itv side: ⊑[itv] directly (no inner collapse). *)
  case Eai : ai => [la ha].
  rewrite Eai /= in Hl_le Hh_le.
  by split.
Qed.

(** *** [reduce p] always satisfies [reduced_shape]. *)
Lemma reduce_reduced_shape (p : collapsed_ad) :
  reduced_shape (reduce p).
Proof.
  case: p => i [r m].
  rewrite /reduce.
  case_eq (non_bottomb i) => Hnb; last first.
  { exact: (RS_bottom bottom is_bottom_bottom). }
  set l := fst i. set h := snd i.
  case_eq (Z.eqb m 0) => Hm0.
  - case_eq (itv_gammab (l, h) r) => Hmem.
    + exact: RS_singleton.
    + exact: (RS_bottom bottom is_bottom_bottom).
  - move/Z.eqb_neq: Hm0 => Hmne.
    set m' := Z.abs m.
    have Hm' : 0 < m' by lia.
    rewrite /build_snapped.
    case_eq (snap_low l r m') => [|l'z] El';
    case_eq (snap_high h r m') => [|h'z] Eh'.
    + apply: RS_interval; [exact Hm' | by [] | by [] | by []].
    + have Hh'z_cong : (m' | h'z - r).
      { move: Eh'. rewrite /snap_high /h. case: (snd i) => [|hz] //=.
        case=> <-. exact: snap_high_z_cong. }
      apply: RS_interval; [exact Hm' | by [] | exact Hh'z_cong | by []].
    + have Hl'z_cong : (m' | l'z - r).
      { move: El'. rewrite /snap_low /l. case: (fst i) => [|lz] //=.
        case=> <-. exact: snap_low_z_cong. }
      apply: RS_interval; [exact Hm' | exact Hl'z_cong | by [] | by []].
    + case_eq (Z.ltb h'z l'z) => Hlt.
      * exact: (RS_bottom bottom is_bottom_bottom).
      * case_eq (Z.eqb l'z h'z) => Heq.
        -- move/Z.eqb_eq: Heq => ?; subst h'z. exact: RS_singleton.
        -- move/Z.ltb_ge: Hlt => Hge.
           move/Z.eqb_neq: Heq => Hneq.
           have Hltz : l'z < h'z by lia.
           have Hl'z_cong : (m' | l'z - r).
           { move: El'. rewrite /snap_low /l. case: (fst i) => [|lz] //=.
             case=> <-. exact: snap_low_z_cong. }
           have Hh'z_cong : (m' | h'z - r).
           { move: Eh'. rewrite /snap_high /h. case: (snd i) => [|hz] //=.
             case=> <-. exact: snap_high_z_cong. }
           apply: RS_interval;
             [exact Hm' | exact Hl'z_cong | exact Hh'z_cong | exact Hltz].
Qed.

(** *** MaximallyReduced of [reduce p]. *)
Lemma reduced_shape_maximally_reduced (a : collapsed_ad) :
  reduced_shape a -> MaximallyReduced a.
Proof.
  case=> {a}.
  - move=> p Hbot.
    have Hempty : γ[collapsed_ad] p ⊆⊇ ∅ := is_bottom_gamma_empty p Hbot.
    apply: (CollapsedBottom.is_empty_maximally_reduced prod_ajsl).
    exact: Hempty.
  - move=> r. exact: singleton_maximally_reduced.
  - move=> l h r m Hm Hl Hh Hlh.
    exact: RS_interval_maximally_reduced.
Qed.

(** *** [MaximallyReduced] of [reduce p]. *)
Lemma reduce_maximally_reduced (p : collapsed_ad) :
  MaximallyReduced (A := collapsed_ad) (reduce p).
Proof.
  apply: reduced_shape_maximally_reduced. exact: reduce_reduced_shape.
Qed.

(** *** [BestAbstraction] of [reduce p] via the two halves above. *)
Lemma reduce_best_abstraction (p : collapsed_ad) :
  BestAbstraction (A := collapsed_ad) (reduce p) (γ[collapsed_ad] p).
Proof.
  apply: best_abstraction_equiv.
  - exact: reduce_maximally_reduced.
  - exact: reduce_preserves_gamma.
Qed.

(** ** Splitting [IsAlpha] over the reduced product.

    [IsAlpha] on the reduced product splits into its two components. The
    single [CollapsedBottom] layer on the product collapses away for a
    non-empty [S], leaving the plain [Conjunction] of [itv] and
    [cong_ad]. This is a generic helper used by the transfer-function
    proofs (e.g. add, rem). *)
Lemma ajsl_is_alpha_split (i : interval) (c : Z * Z) (S : ℘ Z) :
  (exists z, z ∈ S) ->
  IsAlpha (A:=collapsed_ad) (i, c) S <->
  IsAlpha (A:=itv) i S /\ IsAlpha (A:=cong_ad) c S.
Proof.
  move=> Hne.
  rewrite (CollapsedBottom.collapsedbottom_is_alpha prod_ajsl (i, c) S Hne).
  exact: (Conjunction.is_alpha_pair_iff itv cong_ajsl i c S).
Qed.

(* The [Z.add] transfer function (add / add_sound / add_alpha_complete)
   lives in Transfer_function/ZIntervalCongruence/AddTheory.v. *)

(** * Layer stack over the plain product [itv × cong].

    Built over *plain* [itv] — which already has full [JoinIsLUB]
    ([itv_join_is_lub]) — so empties are not collapsed until the bottom
    layers. [prod_ajsl] is the single product base shared by the [reduce]
    machinery above (whose order is widened by [collapsed_ad =
    CollapsedBottom.ad prod_ajsl]) and by the subset layers below.

    Two independent concerns are kept separate (see [AbstractionCombination]):
    order-widening for γ-empty elements ([CollapsedBottom], used only by
    [reduce]/[collapsed_ad]); and the *final* domain, built as a subset of
    the product whose only bottoms are the canonical [is_bottom] ones, with
    a bottom-absorbing join.

    The two user-facing domains, both with [JoinIsLUB]:

    - [non_bottom_zic] : the *non-bottom* ZIntervalCongruence — the
                         maximally-reduced elements of [itv × cong]. Since
                         maximal reduction implies a non-empty γ (∅ has no
                         best abstraction here), this is exactly the subset
                         of [nbitv × cong] of maximally-reduced elements.
                         Total transfer functions (e.g. [add_reduced]) take
                         and return [non_bottom_zic].
    - [zic]            : the *possibly-bottom* ZIntervalCongruence — the
                         subset of [itv × cong] of elements that are
                         maximally reduced *or* have an [is_bottom] (empty)
                         interval. Bottom is the single sentinel
                         [bottom = ((1,0),(0,0))], so the carrier extracts
                         flat with an O(1) [is_bottomb] test. Possibly-empty
                         transfer functions (e.g. [rem_final]) and [reduce]'s
                         landing return [zic].

    [zic_inject] / [zic_case] translate between them.

    Construction (proofs only; all [Subset] layers erase at extraction):

    - L0 [prod_ajsl]         : plain componentwise product, full [JoinIsLUB].
    - L1 [nonempty_prod_ajsl]: its γ-non-empty subset (non-emptiness is
                               carried structurally, so the L2 [add]-closure
                               proof has no bottom/empty cases).
    - L2 [non_bottom_zic]    : the maximally-reduced elements of L1.
    - L3 [zic_ajsl] / [zic]  : the maximally-reduced elements of
                               [cbot_ajsl = CanonicalBottom.ajsl prod_ajsl
                               is_bottomb …] (the canonical-bottom product
                               with a bottom-absorbing join). Members are
                               exactly [final_pred].

    Separately, [reduce]/[collapsed_ad] use a [CollapsedBottom] widening
    of the same [prod_ajsl] (it is the engine that snaps a raw product to
    a [zic] member; see [reduce_final]). *)

(* nonempty_pred a := exists c, c ∈ γ[prod_ajsl] a. *)
Definition nonempty_pred := (NonEmpty.pred prod_ajsl).

Lemma nonempty_join_closure (a1 a2 : prod_ajsl) :
  nonempty_pred a1 -> nonempty_pred a2 ->
  nonempty_pred (ajsl_join prod_ajsl a1 a2).
Proof.
  move=> [c1 Hc1] _. exists c1.
  have Hsub : γ[prod_ajsl] a1 ⊆ γ[prod_ajsl] (ajsl_join prod_ajsl a1 a2).
  { apply: ad_γ_order_preserving. apply: ajsl_join_compat_l. }
  unfold_set in *. exact: (Hsub c1 Hc1).
Qed.

Definition nonempty_prod_ajsl : abstract_join_semilattice Z :=
  NonEmpty.ajsl prod_ajsl nonempty_pred nonempty_join_closure.

Instance nonempty_prod_join_is_lub : JoinIsLUB nonempty_prod_ajsl.
Proof. exact: Subset.Subset_JoinIsLUB. Qed.

(* L2 *)
Definition non_bottom_zic : abstract_join_semilattice Z :=
  MaximallyReducedSubset.ajsl nonempty_prod_ajsl.

(** ** L3: the final reduced join-semilattice [ajsl] / [zic].

    Its members are exactly [final_pred]: either γ-non-empty and
    maximally reduced, or [is_bottom] (an empty interval — the canonical
    sentinel). It is built (below) as [MaximallyReducedSubset.ajsl] over
    [cbot_ajsl], the canonical-bottom product whose only accepted
    γ-empty representatives are the [is_bottom] ones, with a
    bottom-absorbing join (so [JoinIsLUB] holds) and a widened order
    making every [is_bottom] element a [⊑]-minimum. This is the
    extraction-facing layer: a flat carrier [interval × cong] (the
    nested subset proofs are erased) with [bottom = ((1,0),(0,0))] as
    sentinel and O(1) [is_bottomb] testing.

    [final_pred] is the membership predicate of [zic] (read on the raw
    [prod_ajsl] carrier): [final_of_pred] turns any of its witnesses into
    a [zic] element. The [reduce] machinery above is left intact. *)

Definition final_pred (a : prod_ajsl) : Prop :=
  (nonempty_pred a /\ MaximallyReduced (A:=prod_ajsl) a) \/ is_bottom a.

(** *** L3a: canonical-empty product with bottom-absorbing join.

    [cbot_ajsl] is the generalised [CanonicalBottom] over [prod_ajsl]
    whose accepted γ-empty representatives are exactly the [is_bottom]
    ones. It widens the order so every [is_bottom] element is a
    [⊑]-minimum and absorbs them in the join, so [JoinIsLUB] lifts from
    [prod_ajsl]. *)

Lemma is_bottomb_gamma_empty (a : prod_ajsl) :
  is_bottomb a -> γ[prod_ajsl] a ⊆⊇ ∅.
Proof. move=> Hb. exact: (is_bottom_gamma_empty a (elimT (is_bottombP a) Hb)). Qed.

Lemma final_join_closure (a1 a2 : prod_ajsl) :
  NonEmpty.pred prod_ajsl a1 -> NonEmpty.pred prod_ajsl a2 ->
  CanonicalBottom.pred prod_ajsl is_bottomb (ajsl_join prod_ajsl a1 a2).
Proof. move=> H1 H2. left. exact: nonempty_join_closure a1 a2 H1 H2. Qed.

Definition cbot_ajsl : abstract_join_semilattice Z :=
  CanonicalBottom.ajsl prod_ajsl is_bottomb is_bottomb_gamma_empty final_join_closure.

Instance cbot_join_is_lub : JoinIsLUB cbot_ajsl.
Proof. exact: CanonicalBottom.CanonicalBottom_JoinIsLUB. Qed.

(** *** [zic]: the possibly-bottom reduced domain.

    [zic] is the "possibly-bottom ZIntervalCongruence": the subset of
    [itv × cong] of elements that are *maximally reduced, or have an
    [is_bottom] (empty) interval*. Concretely it is the maximally-reduced
    elements of [cbot_ajsl] (the canonical-bottom product), so [JoinIsLUB]
    holds and every [is_bottom] element is the ⊑-minimum. Members are
    exactly [final_pred]: a γ-non-empty maximally-reduced product, or an
    [is_bottom] sentinel. The carrier extracts to a *flat*
    [interval × cong] (the [Subset] proofs are erased), with the single
    sentinel [bottom = ((1,0),(0,0))] and O(1) [is_bottomb]. The
    non-bottom counterpart is [non_bottom_zic] (above); [zic_inject] /
    [zic_case] translate between them. *)
Definition zic_ajsl : abstract_join_semilattice Z :=
  MaximallyReducedSubset.ajsl cbot_ajsl.

Instance zic_join_is_lub : JoinIsLUB zic_ajsl.
Proof. exact: MaximallyReducedSubset.MaximallyReducedSubset_JoinIsLUB. Qed.

(** Abstract-domain view of [zic_ajsl]. *)
Definition zic : abstract_domain Z := zic_ajsl.

(** Any [is_bottomb] element of [cbot_ajsl] is a [⊑]-minimum, hence
    maximally reduced. *)
Lemma cbot_is_bottomb_mr (x : cbot_ajsl) :
  is_bottomb (`x) -> MaximallyReduced (A:=cbot_ajsl) x.
Proof. move=> Hb. split; first by []. move=> a' _. by left. Qed.

(** *** [final_pred] → [zic] bridge.

    A [final_pred] witness for [a] builds the nested [zic] element
    [a]: the [pred] of [cbot_ajsl] holds (non-empty or [is_bottomb]), and
    [a] is maximally reduced in [cbot_ajsl] (for a non-empty [a] this is
    transported from [prod_ajsl]; for an [is_bottom] [a] it is
    [cbot_is_bottomb_mr]). This is the single landing point used by every
    transfer function. *)
Lemma final_pred_cbot (a : prod_ajsl) :
  final_pred a -> CanonicalBottom.pred prod_ajsl is_bottomb a.
Proof. case=> [[Hne _] | Hbot]; [by left | right; exact/is_bottombP]. Qed.

Lemma final_pred_mr (a : prod_ajsl) (H : final_pred a) :
  MaximallyReduced (A:=cbot_ajsl) (exist _ a (final_pred_cbot a H)).
Proof.
  case: H (final_pred_cbot a H) => [[Hne Hmr] | Hbot] Hp.
  - have [Hover Hopt] := proj1 (best_abstraction_iff _ _) Hmr.
    apply/best_abstraction_iff. split; first exact: Hover.
    move=> [a'0 Hp'] Ha'.
    rewrite /(_ ⊑[cbot_ajsl] _) /= /CanonicalBottom.is_included /=.
    right. exact: (Hopt a'0 Ha').
  - apply: cbot_is_bottomb_mr. exact/is_bottombP.
Qed.

Definition final_of_pred (a : prod_ajsl) (H : final_pred a) : zic :=
  exist _ (exist _ a (final_pred_cbot a H)) (final_pred_mr a H).

Definition bottom_final : zic :=
  final_of_pred bottom (or_intror is_bottom_bottom).

(** ** Translating between [non_bottom_zic] and [zic].

    Both domains share the same raw [prod_ajsl] carrier (all [Subset]
    layers erase at extraction); these accessors and the
    [zic_inject]/[zic_project] pair are the bridge. *)

(** Raw [prod_ajsl] carrier of a [zic] / [non_bottom_zic] element. *)
Definition zic_car (z : zic) : prod_ajsl := proj1_sig (proj1_sig z).
Definition nb_car (x : non_bottom_zic) : prod_ajsl := proj1_sig (proj1_sig x).

(** Maximal reduction coincides on the [nonempty_prod_ajsl] subtype and
    the base [prod_ajsl]: an over-approximation of a non-empty set is
    itself non-empty, so the optimality quantifier loses nothing. *)
Lemma mr_nonempty_iff_prod (a : prod_ajsl) (p : nonempty_pred a) :
  MaximallyReduced (A:=nonempty_prod_ajsl) (exist _ a p) <->
  MaximallyReduced (A:=prod_ajsl) a.
Proof.
  split.
  - move=> [_ Hopt]. split; first done.
    move=> a' Ha'.
    have p' : nonempty_pred a'.
    { have [c Hc] := p. exists c.
      have Hsub : γ[prod_ajsl] a ⊆ γ[prod_ajsl] a' by exact: Ha'.
      unfold_set in *. exact: (Hsub c Hc). }
    exact: (Hopt (exist _ a' p') Ha').
  - move=> [_ Hopt]. split; first done.
    move=> [a' p'] Ha'. exact: (Hopt a' Ha').
Qed.

(** Any [prod_ajsl] competitor over-approximating a non-empty γ is itself
    non-empty, hence a [cbot_ajsl] element — so [cbot]-maximal-reduction
    transports back to [prod_ajsl]-maximal-reduction. *)
Lemma cbot_mr_nonempty (x : cbot_ajsl) :
  (exists c, c ∈ γ[prod_ajsl] (`x)) ->
  MaximallyReduced (A:=cbot_ajsl) x ->
  MaximallyReduced (A:=prod_ajsl) (`x).
Proof.
  case: x => a Hp /= Hne Hmr.
  have [_ Hopt] := proj1 (best_abstraction_iff _ _) Hmr.
  apply/best_abstraction_iff. split; first by [].
  move=> a'0 Ha'0.
  have Hp'0 : CanonicalBottom.pred prod_ajsl is_bottomb a'0.
  { left. have [c Hc] := Hne. by exists c; apply: Ha'0. }
  have Hle := Hopt (exist _ a'0 Hp'0) Ha'0.
  move: Hle. rewrite /(_ ⊑[cbot_ajsl] _) /= /CanonicalBottom.is_included /=.
  move=> -[Hb | Hle']; last exact: Hle'.
  exfalso. have [c Hc] := Hne.
  have [He _] := is_bottomb_gamma_empty a Hb. exact: (He c Hc).
Qed.

(** [zic_inject]: view a non-bottom element as a (possibly-bottom) [zic]
    element. γ is unchanged. *)
Definition zic_inject (x : non_bottom_zic) : zic.
Proof.
  case: x => [[a p] m].
  exact: (final_of_pred a (or_introl (conj p (proj1 (mr_nonempty_iff_prod a p) m)))).
Defined.

Lemma zic_inject_gamma (x : non_bottom_zic) :
  γ[zic] (zic_inject x) ⊆⊇ γ[non_bottom_zic] x.
Proof. case: x => [[a p] m]. reflexivity. Qed.

(** [zic_project]: recover the non-bottom element from a [zic] element
    known not to be [is_bottomb]. γ is unchanged. *)
Definition zic_project (z : zic) (Hnb : ~~ is_bottomb (zic_car z)) : non_bottom_zic.
Proof.
  have Hne : nonempty_pred (zic_car z).
  { apply: (CanonicalBottom.pred_not_bot_nonempty prod_ajsl is_bottomb
             (zic_car z) (proj2_sig (proj1_sig z))).
    by move/negbTE: Hnb => ->. }
  refine (exist _ (exist _ (zic_car z) Hne) _).
  apply/(mr_nonempty_iff_prod (zic_car z) Hne).
  exact: (cbot_mr_nonempty (proj1_sig z) Hne (proj2_sig z)).
Defined.

(** ** Landing a raw result into [zic] via [reduce].

    [reduce_final] is the canonical way for a transfer function to land
    a freshly-computed raw element into the maximally-reduced
    collapsed-bottom domain [zic]: it post-composes with [reduce],
    whose output is already maximally reduced (or [is_bottom]). This is
    the bottom-carrying counterpart of how [add_reduced] lands in the
    non-bottom [non_bottom_zic]; it is reused by every transfer function
    whose result can be empty (e.g. [rem]). *)

(** For a γ-non-empty element the [CollapsedBottom] order does not change
    maximal reduction: the collapse only re-orders γ-empty elements. *)
Lemma collapsed_mr_nonempty (p : prod_ajsl) :
  (exists c, c ∈ γ[prod_ajsl] p) ->
  MaximallyReduced (A:=collapsed_ad) p <-> MaximallyReduced (A:=prod_ajsl) p.
Proof.
  move=> Hne.
  rewrite /MaximallyReduced -2!is_alpha_iff_best_abstraction.
  exact: (CollapsedBottom.collapsedbottom_is_alpha prod_ajsl p (γ[prod_ajsl] p) Hne).
Qed.

(** Every [reduced_shape] value is either γ-non-empty or [is_bottom]:
    [RS_bottom] is the latter; [RS_singleton]/[RS_interval] exhibit a
    witness via [RS_interval_witness]. *)
Lemma reduced_shape_nonempty_or_bottom (p : collapsed_ad) :
  reduced_shape p -> (exists c, c ∈ γ[prod_ajsl] p) \/ is_bottom p.
Proof.
  case=> {p}.
  - move=> p Hbot. by right.
  - move=> r. left. exists r. split.
    + apply/itv_gammaP.
      rewrite /itv_gammab /=. apply/andP; split; apply/Z.leb_spec0; lia.
    + by apply/gamma_singleton.
  - move=> l h r m Hm Hl Hh Hlh. left.
    have [x [_ [Hx _]]] := RS_interval_witness l h r m Hm Hl Hh Hlh.
    by exists x.
Qed.

(** [reduce p] satisfies [final_pred]: it is [is_bottom], or γ-non-empty
    and maximally reduced (the latter transported from [collapsed_ad] to
    [prod_ajsl] by [collapsed_mr_nonempty]). *)
Lemma reduce_final_pred (p : collapsed_ad) : final_pred (reduce p).
Proof.
  case: (reduced_shape_nonempty_or_bottom (reduce p) (reduce_reduced_shape p))
    => [Hne | Hbot].
  - left. split; first exact: Hne.
    apply/(collapsed_mr_nonempty (reduce p) Hne).
    exact: reduce_maximally_reduced p.
  - by right.
Qed.

Definition reduce_final (p : collapsed_ad) : zic :=
  final_of_pred (reduce p) (reduce_final_pred p).

(** [reduce_final] preserves γ (it only sharpens, by [reduce]). γ passes
    through both [Subset] layers unchanged. *)
Lemma reduce_final_gamma (p : collapsed_ad) :
  γ[zic] (reduce_final p) ⊆⊇ γ[collapsed_ad] p.
Proof. exact: reduce_preserves_gamma p. Qed.

(** [reduce_final p] is the best abstraction of [γ p] on [zic]. The
    optimum from [reduce_best_abstraction] (on [collapsed_ad]) lifts
    through the two [Subset] layers: γ is unchanged, and the only order
    difference is [is_empty] vs [is_bottomb] in the minimal disjunct —
    reconciled because a γ-empty [reduce p] is [is_bottom]. *)
Lemma reduce_final_best (p : collapsed_ad) :
  BestAbstraction (A:=zic) (reduce_final p) (γ[collapsed_ad] p).
Proof.
  have [Hover Hopt] := proj1 (best_abstraction_iff _ _) (reduce_best_abstraction p).
  apply/best_abstraction_iff. split.
  - exact: Hover.
  - move=> [[a'0 Hp'] Hmr'] Ha'.
    rewrite /(_ ⊑[zic] _) /= /CanonicalBottom.is_included /=.
    case: (Hopt a'0 Ha') => [Hemp | Hle']; last by right.
    left. apply/is_bottombP.
    case: (reduced_shape_nonempty_or_bottom (reduce p) (reduce_reduced_shape p))
      => [Hne | //].
    exfalso. case: Hne => c Hc. exact: (proj1 Hemp c Hc).
Qed.

(** ** Singleton detection.

    [is_singleton a = Some n] when the interval component of [a] is the
    point interval [[n,n]], which forces [γ a ⊆ {n}] — every concrete
    value is [n]. (It does *not* assert [n ∈ γ a]: the congruence
    component may still rule [n] out, leaving [γ a] empty. Soundness as a
    "γ refines to at most {n}" certificate is all that is needed.) The
    test only inspects the interval, so it is computable and cheap; it is
    the building block for "constant operand" transfer-function cases
    (e.g. a constant divisor in [Z.rem]). *)
Definition is_singleton (a : prod_ajsl) : option Z :=
  let (l, h) := fst a in Z_interval.is_singleton l h.

Lemma is_singleton_sound (a : prod_ajsl) (n : Z) :
  is_singleton a = Some n -> forall c, c ∈ γ[prod_ajsl] a -> c = n.
Proof.
  case: a => [[l h] cm]. rewrite /is_singleton /=.
  move=> Hs c [Hci _].
  exact: (proj1 (proj1 (is_singleton_spec l h n) Hs c) Hci).
Qed.

(** ** Building maximally-reduced elements from explicit bounds.

    Helpers to construct a genuine [non_bottom_zic] element denoting an
    interval [[l,h]] intersected with a congruence class [r + mℤ]. Reused by
    transfer-function counterexamples that need concrete operands. *)

(** The interval × congruence pair [([l,h], (r,m))] has a non-empty
    concretization as soon as [l <= h] and its lower endpoint lies on the
    congruence class (i.e. [m | l - r]): the point [l] is then in both
    components, hence in [γ]. *)
Lemma interval_cong_nonempty (l h r m : Z) :
  (m | l - r) -> l <= h ->
  nonempty_pred ((WithTop.NotTop l, WithTop.NotTop h), (r, m)).
Proof.
  move=> Hl Hlh. exists l. split.
  - simpl. unfold_set. simpl. lia.
  - simpl. unfold_set. exact: Hl.
Qed.

(** The interval × congruence pair [([l,h], (r,m))] is maximally reduced
    (as a [non_bottom_zic] element) whenever [0 < m], [l < h], and both
    endpoints lie on the congruence class [r + mℤ] (i.e. [m | l - r] and
    [m | h - r]). Such a pair is exactly an [RS_interval] shape, so it is
    maximally reduced on [collapsed_ad] ([RS_interval_maximally_reduced]);
    being non-empty, this transports down to [prod_ajsl]
    ([collapsed_mr_nonempty]) and then to the subtype
    ([mr_nonempty_iff_prod]). *)
Lemma interval_cong_maximally_reduced (l h r m : Z)
  (p : nonempty_pred ((WithTop.NotTop l, WithTop.NotTop h), (r, m))) :
  0 < m -> (m | l - r) -> (m | h - r) -> l < h ->
  MaximallyReduced (A:=nonempty_prod_ajsl)
    (exist _ ((WithTop.NotTop l, WithTop.NotTop h), (r, m)) p).
Proof.
  move=> Hm Hl Hh Hlh.
  apply (proj2 (mr_nonempty_iff_prod _ p)).
  apply (proj1 (collapsed_mr_nonempty
                  ((WithTop.NotTop l, WithTop.NotTop h), (r, m)) p)).
  exact: (RS_interval_maximally_reduced
            (WithTop.NotTop l) (WithTop.NotTop h) r m Hm Hl Hh Hlh).
Qed.

(** Build the [non_bottom_zic] element denoting the interval [[l,h]]
    intersected with the congruence class [r + mℤ], for the well-formed
    case [0 < m], [l < h], and both endpoints on [r + mℤ]. Its
    concretization is exactly the set of class points in range,
    [{l, l+m, …, h}]. *)
Definition interval_cong_elt (l h r m : Z)
  (Hm : 0 < m) (Hl : (m | l - r)) (Hh : (m | h - r)) (Hlh : l < h)
  : non_bottom_zic :=
  let p := interval_cong_nonempty l h r m Hl (Z.lt_le_incl _ _ Hlh) in
  exist _ (exist _ ((WithTop.NotTop l, WithTop.NotTop h), (r, m)) p)
          (interval_cong_maximally_reduced l h r m p Hm Hl Hh Hlh).

(** Membership in [interval_cong_elt l h r m] is just being in range and on
    the congruence class — the two components, read off directly. *)
Lemma interval_cong_elt_gammaE (l h r m : Z)
  (Hm : 0 < m) (Hl : (m | l - r)) (Hh : (m | h - r)) (Hlh : l < h) (z : Z) :
  z ∈ γ[non_bottom_zic] (interval_cong_elt l h r m Hm Hl Hh Hlh)
  <-> l <= z <= h /\ (m | z - r).
Proof.
  split.
  - move=> [Hi Hc]. have [? ?] : l <= z /\ z <= h by exact: Hi.
    by split; [lia | exact: Hc].
  - move=> [Hb Hc]. split; last exact: Hc.
    simpl. unfold_set. simpl. lia.
Qed.

