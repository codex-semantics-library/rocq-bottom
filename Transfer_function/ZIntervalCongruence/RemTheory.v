(* STATUS: rem: convention-typed entry point done; sound on all inputs
   (interval + congruence); interval best on three detected cases;
   congruence sound everywhere via the gcd rule.

   [rem_final : non_bottom_zic -> non_bottom_zic -> zic] follows the
   transfer-function convention (non-bottom args, bottom-carrying result).
   It is sound ([rem_final_sound]) for all inputs and *exact* on the
   bottom branch (empty result <-> divisor trivially {0}, the only empty
   case once arguments are non-bottom).

   The result interval is [rem_itv_envelope], which dispatches on three
   detectors and is *best* on each:
   - [const_block]: constant divisor, dividend within a single quotient
     block ([rem_itv_envelope_const_block_best], via [itv_add_const_best]);
   - [narrow_divb]: every dividend value strictly smaller in magnitude
     than every divisor value, so [Z.rem] is the identity
     ([rem_itv_envelope_narrow_best], via [rem_itv_identity_best]);
   - [const_residue]: constant divisor n with |n| dividing the dividend
     modulus m2 and a single-sign dividend, so the remainder is the
     constant rho = +-(r2 mod |n|) even across many quotient blocks
     ([rem_itv_envelope_const_residue_best]; flagship example
     [[0,100] cap (3 + 10Z)] rem {10} = [3,3]).
   It is the top interval on all other inputs (sound only).

   The result congruence is [rem_cong]: [(r2, gcd m2 (gcd r1 m1))],
   sound for every input pair ([rem_cong_sound], from the algebraic rule
   [rem_cong_divide]). Remaining precision work: the general interval
   envelope (const-divisor multi-block, non-constant bounded divisors),
   and bestness of the congruence beyond the trivial regimes.

   The old [collapsed_ad]-typed [rem_itv] (and its WithBottom interval result)
   are kept for now as scaffolding toward that envelope. *)


From Stdlib Require Import ZArith Lia Zquot.
Require Import ssreflect ssrbool.
Require Import
  base Abstraction AbstractLattice
  AbstractionCombination
  Z_interval Congruence
  ZIntervalCongruence.

Open Scope Z_scope.

(** ** Z.rem transfer function.

    [Z.rem] is the truncated-division remainder: it has the sign of the
    dividend and satisfies [|Z.rem c d| < |d|] for [d <> 0]. We aim for a
    best transfer function written directly on the product, since the
    result interval depends on the input congruences and vice versa.

    This block collects the foundational arithmetic facts about [Z.rem];
    later definitions (the interval and congruence components) build on
    them. They are pure [ZArith] and make no reference to the abstract
    domains. *)

(* Note: status is in ethereal-cooking-lerdorf, session
   42c6368a-2493-47ee-9f03-55ab18b264f0. *)

(** [Z.rem] uses [|d|] as its modulus: it is invariant under the sign of
    the divisor. *)
Lemma Z_rem_abs_r (c d : Z) : Z.rem c (Z.abs d) = Z.rem c d.
Proof.
  case: (Z.le_gt_cases 0 d) => Hd.
  - by rewrite Z.abs_eq.
  - by rewrite (Z.abs_neq d ltac:(lia)) (Z.rem_opp_r c d ltac:(lia)).
Qed.

(** Sign and magnitude of [Z.rem]: a non-negative dividend yields a
    remainder in [[0, |d|)]; a non-positive dividend yields one in
    [(-|d|, 0]]. *)
Lemma Z_rem_bounds (c d : Z) : d <> 0 ->
  (0 <= c -> 0 <= Z.rem c d < Z.abs d) /\
  (c <= 0 -> - Z.abs d < Z.rem c d <= 0).
Proof.
  move=> Hd.
  have He : 0 < Z.abs d by lia.
  rewrite -Z_rem_abs_r.
  set e := Z.abs d in He *.
  have Hne : e <> 0 by lia.
  split=> Hc.
  - exact: Z.rem_bound_pos c e Hc He.
  - rewrite -(Z.opp_involutive c) (Z.rem_opp_l _ _ Hne).
    have Hb := Z.rem_bound_pos (- c) e ltac:(lia) He.
    lia.
Qed.

(** When the dividend is strictly smaller in magnitude than the divisor,
    [Z.rem] is the identity. This is what lets the divisor interval
    recognise [rem] as a no-op on a narrow dividend. *)
Lemma Z_rem_small_abs (c d : Z) : Z.abs c < Z.abs d -> Z.rem c d = c.
Proof.
  move=> Hlt.
  have He : 0 < Z.abs d by lia.
  rewrite -Z_rem_abs_r. set e := Z.abs d in He Hlt *.
  have Hne : e <> 0 by lia.
  case: (Z.le_gt_cases 0 c) => Hc.
  - apply: Z.rem_small. lia.
  - have Hs : Z.rem (-c) e = -c by apply: Z.rem_small; lia.
    by rewrite -(Z.opp_involutive c) (Z.rem_opp_l _ _ Hne) Hs.
Qed.

(** [|Z.rem c d| < |d|] for a nonzero divisor. *)
Lemma Z_rem_abs_lt (c d : Z) : d <> 0 -> Z.abs (Z.rem c d) < Z.abs d.
Proof.
  move=> Hd. have [Hpos Hneg] := Z_rem_bounds c d Hd.
  case: (Z.le_gt_cases 0 c) => Hc.
  - have := Hpos Hc. lia.
  - have := Hneg ltac:(lia). lia.
Qed.

(** [|Z.rem c d| <= |c|]: the remainder never exceeds the dividend in
    magnitude. *)
Lemma Z_rem_abs_le_l (c d : Z) : d <> 0 -> Z.abs (Z.rem c d) <= Z.abs c.
Proof.
  move=> Hd.
  case: (Z.lt_ge_cases (Z.abs c) (Z.abs d)) => Hcd.
  - rewrite (Z_rem_small_abs c d Hcd). lia.
  - have := Z_rem_abs_lt c d Hd. lia.
Qed.

(** *** Identity / narrow case.

    When every dividend value is strictly smaller in magnitude than every
    nonzero divisor value, [Z.rem] acts as the identity, so the result set
    is exactly [γ[collapsed_ad] a2]. This is the case where the *divisor interval*
    certifies that [rem] is a no-op — a refinement visible only on the
    product. *)

Lemma rem_collecting_identity (a2 a1 : collapsed_ad) :
  (exists c1, c1 ∈ γ[collapsed_ad] a1 /\ c1 <> 0) ->
  (forall c2, c2 ∈ γ[collapsed_ad] a2 ->
   forall c1, c1 ∈ γ[collapsed_ad] a1 -> c1 <> 0 -> Z.abs c2 < Z.abs c1) ->
  collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
    (γ[collapsed_ad] a2) (γ[collapsed_ad] a1) ⊆⊇ γ[collapsed_ad] a2.
Proof.
  move=> [d1 [Hd1 Hd1ne]] Hnarrow.
  apply propset_equiv_iff => x. split.
  - move=> [c2 [c1 [Hc2 [Hc1 [Hc1ne Heq]]]]].
    have Hsmall := Hnarrow c2 Hc2 c1 Hc1 Hc1ne.
    rewrite (Z_rem_small_abs c2 c1 Hsmall) in Heq.
    by rewrite -Heq.
  - move=> Hx.
    exists x, d1.
    split; [exact: Hx | split; [exact: Hd1 | split; [exact: Hd1ne |]]].
    exact: Z_rem_small_abs x d1 (Hnarrow x Hx d1 Hd1 Hd1ne).
Qed.

(** In the identity case the best result interval is just the dividend's
    interval component [fst a2], since [a2] is maximally reduced. *)
Lemma rem_itv_identity_best (a2 a1 : collapsed_ad) :
  MaximallyReduced a2 ->
  (exists c2, c2 ∈ γ[collapsed_ad] a2) ->
  (exists c1, c1 ∈ γ[collapsed_ad] a1 /\ c1 <> 0) ->
  (forall c2, c2 ∈ γ[collapsed_ad] a2 ->
   forall c1, c1 ∈ γ[collapsed_ad] a1 -> c1 <> 0 -> Z.abs c2 < Z.abs c1) ->
  BestAbstraction (A:=itv) (fst a2)
    (collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
       (γ[collapsed_ad] a2) (γ[collapsed_ad] a1)).
Proof.
  case: a2 => i2 c2 /= Hred Hne2 Hne1 Hnarrow.
  have Halpha : IsAlpha (A:=collapsed_ad) (i2, c2) (γ[collapsed_ad] (i2, c2))
    := best_abstraction_is_is_alpha _ _ Hred.
  have [Hi _] := proj1 (ajsl_is_alpha_split i2 c2 _ Hne2) Halpha.
  have Hbest : BestAbstraction (A:=itv) i2 (γ[collapsed_ad] (i2, c2))
    := is_alpha_is_best_abstraction _ _ Hi.
  have Heq := rem_collecting_identity (i2, c2) a1 Hne1 Hnarrow.
  apply: (best_abstraction_equiv (A:=itv) i2 _ _ Hbest).
  by symmetry.
Qed.

(** *** Constant-divisor, single-block case.

    When the divisor abstraction is a constant [n] and the dividend lies
    entirely within one quotient block (i.e. [Z.quot c2 n] is a constant
    [q] across [γ[collapsed_ad] a2]), [Z.rem c2 n] is the affine map
    [c2 ↦ c2 - n*q]. The result set is then [γ[collapsed_ad] a2] shifted by
    [-(n*q)] — exactly the collecting sum with the singleton [{-(n*q)}],
    so the best interval is obtained by interval addition of a constant. *)

(** [Z.rem] in terms of [Z.quot]. *)
Lemma Z_rem_quot_eq (c n : Z) : Z.rem c n = c - n * Z.quot c n.
Proof. have := Z.quot_rem' c n. lia. Qed.

(** [Z.quot _ n] is constant across an interval whose two endpoints share
    the same quotient: since [Z.quot] (truncation toward zero) is monotone
    in the dividend for fixed [n], equal quotients at the endpoints squeeze
    every value in between to that same block. This is the certificate the
    constant-divisor [rem] case uses to read [q] off the dividend interval. *)
Lemma Z_quot_const_on_interval (l h n c : Z) :
  l <= c <= h -> Z.quot l n = Z.quot h n -> Z.quot c n = Z.quot l n.
Proof.
  move=> [Hlc Hch] Heq.
  case: (Z.lt_trichotomy n 0) => [Hn | [Hn | Hn]].
  - have R : forall x, Z.quot x n = - Z.quot x (- n).
    { move=> x. by rewrite -(Zquot_opp_r x (- n)) Z.opp_involutive. }
    rewrite !R in Heq *.
    have H1 := Z_quot_monotone l c (- n) ltac:(lia) Hlc.
    have H2 := Z_quot_monotone c h (- n) ltac:(lia) Hch.
    lia.
  - subst n. by rewrite !Zquot_0_r.
  - have H1 := Z_quot_monotone l c n ltac:(lia) Hlc.
    have H2 := Z_quot_monotone c h n ltac:(lia) Hch.
    lia.
Qed.

Lemma rem_collecting_const_block (a2 a1 : collapsed_ad) (n q : Z) :
  n <> 0 ->
  (exists c1, c1 ∈ γ[collapsed_ad] a1) ->
  (forall c1, c1 ∈ γ[collapsed_ad] a1 -> c1 = n) ->
  (forall c2, c2 ∈ γ[collapsed_ad] a2 -> Z.quot c2 n = q) ->
  collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
    (γ[collapsed_ad] a2) (γ[collapsed_ad] a1)
  ⊆⊇ collecting_binary_forward Z.add (γ[collapsed_ad] a2) {[ x | x = - (n * q) ]}.
Proof.
  move=> Hn [d1 Hd1] Hconst Hblock.
  apply propset_equiv_iff => x. split.
  - move=> [c2 [c1 [Hc2 [Hc1 [_ Heq]]]]].
    have Hc1n := Hconst c1 Hc1. subst c1.
    rewrite (Z_rem_quot_eq c2 n) (Hblock c2 Hc2) in Heq.
    exists c2, (- (n * q)).
    split; [exact: Hc2 | split; [by apply/propset_elem_of_iff | lia]].
  - move=> [c2 [k [Hc2 [Hk Hsum]]]].
    move/propset_elem_of_iff: Hk => Hk.
    have Hd1n := Hconst d1 Hd1.
    exists c2, n.
    split; [exact: Hc2 | split; [by rewrite -Hd1n | split; [exact: Hn |]]].
    rewrite (Z_rem_quot_eq c2 n) (Hblock c2 Hc2). lia.
Qed.

(** *** Adding a constant to an interval.

    [itv_add_const K i] adds [K] to both bounds of [i] ([Top] bounds stay
    [Top]). It is the abstract counterpart of [c ↦ c + K]. *)

Definition add_const_bound (K : Z) (b : WithTop.with_top Z) : WithTop.with_top Z :=
  match b with
  | WithTop.Top => WithTop.Top
  | WithTop.NotTop z => WithTop.NotTop (z + K)
  end.

Definition itv_add_const (K : Z) (i : interval) : interval :=
  (add_const_bound K (fst i), add_const_bound K (snd i)).

Lemma Zleb_add_l (a b K : Z) : (a + K <=? b) = (a <=? b - K).
Proof. apply/idP/idP => /Z.leb_le ?; apply/Z.leb_le; lia. Qed.

Lemma Zleb_add_r (a b K : Z) : (b <=? a + K) = (b - K <=? a).
Proof. apply/idP/idP => /Z.leb_le ?; apply/Z.leb_le; lia. Qed.

Lemma itv_add_const_compose (a b : Z) (i : interval) :
  itv_add_const a (itv_add_const b i) = itv_add_const (b + a) i.
Proof.
  by case: i => [[|l] [|h]]; rewrite /itv_add_const /add_const_bound /= ?Z.add_assoc.
Qed.

Lemma itv_add_const_0 (i : interval) : itv_add_const 0 i = i.
Proof.
  by case: i => [[|l] [|h]]; rewrite /itv_add_const /add_const_bound /= ?Z.add_0_r.
Qed.

Lemma itv_gammab_add_const (K : Z) (i : interval) (y : Z) :
  itv_gammab (itv_add_const K i) y = itv_gammab i (y - K).
Proof.
  case: i => l h.
  rewrite /itv_add_const /itv_gammab /add_const_bound /lub_gammab /glb_gammab /=.
  case: l => [|l]; case: h => [|h] //=.
  - by rewrite Zleb_add_r.
  - by rewrite Zleb_add_l.
  - by rewrite Zleb_add_l Zleb_add_r.
Qed.

Lemma itv_add_const_gamma (K : Z) (i : interval) (y : Z) :
  y ∈ γ[itv] (itv_add_const K i) <-> (y - K) ∈ γ[itv] i.
Proof.
  split => H.
  - apply/itv_gammaP. move/itv_gammaP: H => H.
    by rewrite itv_gammab_add_const in H.
  - apply/itv_gammaP. rewrite itv_gammab_add_const.
    by move/itv_gammaP: H.
Qed.

(** *** Best abstraction of adding a constant.

    Adding a fixed [K] to every element of [S] is mirrored on intervals by
    [itv_add_const K]: if [i] is the best interval for [S], then
    [itv_add_const K i] is the best interval for the collecting [Z.add] of
    [S] with the singleton [{K}] (i.e. [S + {K}]). This is the abstract
    counterpart of [c ↦ c + K], and the engine behind the constant-divisor
    [rem] case below (with [K = -(n*q)]). Modelled on
    [Z_interval.best_abstraction_opp]. *)
Lemma itv_add_const_best (K : Z) (i : interval) (S : ℘ Z) :
  BestAbstraction (A:=itv) i S ->
  BestAbstraction (A:=itv) (itv_add_const K i)
    (collecting_binary_forward Z.add S {[ x | x = K ]}).
Proof.
  move=> [Hsound Hopt]; apply best_abstraction_iff; split.
  - (* Soundness: z = c2 + K with c2 ∈ S ⊆ γ i, so z ∈ γ(itv_add_const K i). *)
    move=> z [c2 [c1 [Hc2 [Hc1 Heq]]]].
    move/propset_elem_of_iff: Hc1 => ?; subst c1.
    apply/itv_add_const_gamma.
    have -> : z - K = c2 by lia.
    exact: Hsound.
  - (* Optimality: shift any competitor b back by -K to land below S. *)
    move=> b Hb.
    have Hb' : Overapproximates (A:=itv) (itv_add_const (- K) b) S.
    { move=> s Hs; apply/itv_add_const_gamma.
      have -> : s - - K = s + K by lia.
      apply: Hb. exists s, K.
      split; [exact: Hs | split; [by apply/propset_elem_of_iff | lia]]. }
    move: (Hopt _ Hb') => {Hsound Hopt Hb Hb'}.
    rewrite /itv_add_const /add_const_bound.
    move: i b => [[|li] [|hi]] [[|lb] [|hb]] //=; try lia.
    all: rewrite /BoundAbstraction.GLB.glb_is_included; lia.
Qed.

(** *** Constant-divisor, single-block case — best interval.

    When the divisor is a known constant [n] and the dividend lies in one
    quotient block ([Z.quot c2 n = q] throughout [γ a2]), [Z.rem] is the
    affine map [c2 ↦ c2 - n*q]; the best result interval is then the
    dividend's interval [fst a2] shifted by [-(n*q)]. Combines
    [rem_collecting_const_block] with [itv_add_const_best]. *)
Lemma rem_itv_const_block_best (a2 a1 : collapsed_ad) (n q : Z) :
  MaximallyReduced a2 ->
  (exists c2, c2 ∈ γ[collapsed_ad] a2) ->
  n <> 0 ->
  (exists c1, c1 ∈ γ[collapsed_ad] a1) ->
  (forall c1, c1 ∈ γ[collapsed_ad] a1 -> c1 = n) ->
  (forall c2, c2 ∈ γ[collapsed_ad] a2 -> Z.quot c2 n = q) ->
  BestAbstraction (A:=itv) (itv_add_const (- (n * q)) (fst a2))
    (collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
       (γ[collapsed_ad] a2) (γ[collapsed_ad] a1)).
Proof.
  case: a2 => i2 c2 /= Hred Hne2 Hn Hne1 Hconst Hblock.
  have Halpha : IsAlpha (A:=collapsed_ad) (i2, c2) (γ[collapsed_ad] (i2, c2))
    := best_abstraction_is_is_alpha _ _ Hred.
  have [Hi _] := proj1 (ajsl_is_alpha_split i2 c2 _ Hne2) Halpha.
  have Hbest : BestAbstraction (A:=itv) i2 (γ[collapsed_ad] (i2, c2))
    := is_alpha_is_best_abstraction _ _ Hi.
  apply: (best_abstraction_equiv (A:=itv) (itv_add_const (- (n * q)) i2)).
  - exact: (itv_add_const_best (- (n * q)) i2 _ Hbest).
  - symmetry.
    exact: (rem_collecting_const_block (i2, c2) a1 n q Hn Hne1 Hconst Hblock).
Qed.

(** *** Best result interval [rem_itv].

    [rem_itv a2 a1] is the best interval over-approximating the partial
    collecting [Z.rem] set. Since [itv] has no [⊑]-minimum (γ-empty
    intervals are not below every interval), the result is wrapped in
    [WithBottom]: [Bot] is the best abstraction of the empty result.

    The empty result arises exactly when either operand is [is_bottom],
    or the divisor abstraction concretizes into [{0}] (no valid divisor
    under the partial semantics). All other inputs go to
    [rem_itv_envelope], the genuine best interval for a non-empty result
    — currently a sound placeholder (the top interval); replacing it and
    proving [rem_itv_envelope_best] is the remaining work (case 2). *)

(** [γ[collapsed_ad] a1 ⊆ {0}]: detected via the interval component being the
    point interval [[0,0]] (or [a1] being γ-empty). Sound for *any* [a1],
    not just reduced ones, because [γ[collapsed_ad]] refines the interval γ. *)
Definition divisor_trivialb (a1 : collapsed_ad) : bool :=
  is_bottomb a1 ||
  match fst a1 with
  | (WithTop.NotTop l, WithTop.NotTop h) => (l =? 0) && (h =? 0)
  | _ => false
  end.

Lemma divisor_trivial_empty (a1 : collapsed_ad) :
  divisor_trivialb a1 -> forall c1, c1 ∈ γ[collapsed_ad] a1 -> c1 = 0.
Proof.
  move=> Ht c1 Hc1.
  move: Ht. rewrite /divisor_trivialb => /orP [Hb | Hz].
  - exfalso.
    move/is_bottombP: Hb => Hbot.
    have := proj1 (is_bottom_gamma_empty a1 Hbot) c1 Hc1. by [].
  - move: Hz Hc1. case: a1 => [[l h] c]. rewrite /fst.
    case: l => [|lz] //; case: h => [|hz] //.
    move=> /andP [/Z.eqb_eq -> /Z.eqb_eq ->] [Hc1i _].
    move/itv_gammaP: Hc1i.
    rewrite /itv_gammab /glb_gammab /lub_gammab => /andP [Hle Hge].
    move: Hle Hge => /Z.leb_le ? /Z.leb_le ?. lia.
Qed.

(** Interval projection of [γ]: any concrete value of [a] lies in the
    interval component [fst a]. (Casing [a] into a pair makes the product
    γ reduce to its intersection form, which then destructs.) *)
Lemma gamma_fst_itv (a : collapsed_ad) (c : Z) :
  c ∈ γ[collapsed_ad] a -> c ∈ γ[itv] (fst a).
Proof. case: a => [ia ca] [Hi _]. exact: Hi. Qed.

(** *** Constant-divisor / single-block detection.

    [const_block a2 a1 = Some (n, q)] when the divisor [a1] is a nonzero
    constant [n] ([is_singleton]) and the dividend's interval [fst a2] lies
    within a single [Z.quot _ n] block (both endpoints have quotient [q]).
    In that case [Z.rem _ n] is the affine map [c2 ↦ c2 - n*q] over
    [γ a2], whose best interval is [fst a2] shifted by [-(n*q)]. *)
Definition const_block (a2 a1 : collapsed_ad) : option (Z * Z) :=
  match is_singleton a1 with
  | Some n =>
      if n =? 0 then None
      else match fst a2 with
           | (WithTop.NotTop l2, WithTop.NotTop h2) =>
               if Z.quot l2 n =? Z.quot h2 n then Some (n, Z.quot l2 n) else None
           | _ => None
           end
  | None => None
  end.

(** When [const_block] fires it certifies the three facts feeding
    [rem_collecting_const_block] / [rem_itv_const_block_best]: a nonzero
    constant divisor, and a constant dividend quotient [q]. *)
Lemma const_block_some (a2 a1 : collapsed_ad) (n q : Z) :
  const_block a2 a1 = Some (n, q) ->
  n <> 0 /\
  (forall c1, c1 ∈ γ[collapsed_ad] a1 -> c1 = n) /\
  (forall c2, c2 ∈ γ[collapsed_ad] a2 -> Z.quot c2 n = q).
Proof.
  case: a2 => [ia2 ca2]. rewrite /const_block.
  case Hsg: (is_singleton a1) => [m|] //.
  case Hm0: (m =? 0) => //.
  change (fst (ia2, ca2)) with ia2.
  case: ia2 => [[|l2] [|h2]] //.
  case Hq: (Z.quot l2 m =? Z.quot h2 m) => // [= Hmn Hqq].
  subst n q.
  move: Hm0 => /Z.eqb_neq Hm0. move: Hq => /Z.eqb_eq Hq.
  split; [exact: Hm0 | split].
  - exact: is_singleton_sound a1 m Hsg.
  - move=> c2 Hc2.
    move/itv_gammaP: (gamma_fst_itv _ c2 Hc2).
    rewrite /itv_gammab /glb_gammab /lub_gammab => /andP [/Z.leb_le Hle /Z.leb_le Hge].
    have Hb : l2 <= c2 <= h2 by lia.
    exact: Z_quot_const_on_interval l2 h2 m c2 Hb Hq.
Qed.

(** *** Narrow-dividend (identity) detection.

    [narrow_divb a2 a1] certifies, from the interval components alone,
    that every dividend value is strictly smaller in magnitude than every
    divisor value (all of which are then nonzero): the dividend interval
    is bounded, and the divisor interval is single-signed with a magnitude
    lower bound above the dividend's magnitude upper bound. On such inputs
    [Z.rem] is the identity ([Z_rem_small_abs]), so the best result
    interval is the dividend's own interval [fst a2]
    ([rem_itv_identity_best]). This wires the identity math into the
    envelope; it complements [const_block], which covers the same
    situation only for singleton divisors. *)

(** Magnitude lower bound of a single-signed interval: [Some B] guarantees
    [0 < B <= Z.abs c] for every [c] in the interval. *)
Definition itv_abs_min (i : interval) : option Z :=
  match i with
  | (WithTop.NotTop l, WithTop.NotTop h) =>
      if 0 <? l then Some l else if h <? 0 then Some (- h) else None
  | (WithTop.NotTop l, WithTop.Top) => if 0 <? l then Some l else None
  | (WithTop.Top, WithTop.NotTop h) => if h <? 0 then Some (- h) else None
  | (WithTop.Top, WithTop.Top) => None
  end.

Lemma itv_abs_min_spec (i : interval) (B : Z) :
  itv_abs_min i = Some B ->
  0 < B /\ (forall c, c ∈ γ[itv] i -> B <= Z.abs c).
Proof.
  case: i => [[|l] [|h]] //=.
  - (* (Top, NotTop h) *)
    case Hh: (h <? 0) => // [= <-]. move: Hh => /Z.ltb_lt Hh.
    split; first lia.
    move=> c [_ Hhi]. have : c <= h by exact: Hhi. lia.
  - (* (NotTop l, Top) *)
    case Hl: (0 <? l) => // [= <-]. move: Hl => /Z.ltb_lt Hl.
    split; first lia.
    move=> c [Hlo _]. have : l <= c by exact: Hlo. lia.
  - (* (NotTop l, NotTop h) *)
    case Hl: (0 <? l) => [|]; last case Hh: (h <? 0) => //.
    + move=> [= <-]. move: Hl => /Z.ltb_lt Hl.
      split; first lia.
      move=> c [Hlo _]. have : l <= c by exact: Hlo. lia.
    + move=> [= <-]. move: Hh => /Z.ltb_lt Hh.
      split; first lia.
      move=> c [_ Hhi]. have : c <= h by exact: Hhi. lia.
Qed.

Definition narrow_divb (a2 a1 : collapsed_ad) : bool :=
  match fst a2, itv_abs_min (fst a1) with
  | (WithTop.NotTop l2, WithTop.NotTop h2), Some B =>
      (Z.abs l2 <? B) && (Z.abs h2 <? B)
  | _, _ => false
  end.

(** A dividend in [[-5, 5]] is untouched by a divisor in [[10, 20]]:
    the envelope returns the dividend's interval. *)
Example narrow_divb_example :
  narrow_divb ((WithTop.NotTop (-5), WithTop.NotTop 5), (0, 1))
              ((WithTop.NotTop 10, WithTop.NotTop 20), (0, 1)).
Proof. by vm_compute. Qed.

(** What [narrow_divb] certifies: the divisor values are all nonzero,
    and each strictly exceeds every dividend value in magnitude. *)
Lemma narrow_divb_spec (a2 a1 : collapsed_ad) :
  narrow_divb a2 a1 ->
  (forall c1, c1 ∈ γ[collapsed_ad] a1 -> c1 <> 0) /\
  (forall c2, c2 ∈ γ[collapsed_ad] a2 ->
   forall c1, c1 ∈ γ[collapsed_ad] a1 -> Z.abs c2 < Z.abs c1).
Proof.
  rewrite /narrow_divb.
  case Hi2: (fst a2) => [l2b h2b].
  case: l2b Hi2 => [|l2] Hi2 //; case: h2b Hi2 => [|h2] Hi2 //.
  case HB: (itv_abs_min (fst a1)) => [B|] //.
  move=> /andP [/Z.ltb_lt Hl2 /Z.ltb_lt Hh2].
  have [HBpos HBlow] := itv_abs_min_spec _ _ HB.
  split.
  - move=> c1 Hc1.
    have := HBlow c1 (gamma_fst_itv _ _ Hc1). lia.
  - move=> c2 Hc2 c1 Hc1.
    have HB1 := HBlow c1 (gamma_fst_itv _ _ Hc1).
    have Hitv2 := gamma_fst_itv _ _ Hc2. rewrite Hi2 in Hitv2.
    move: Hitv2 => [Hlo Hhi].
    have : l2 <= c2 by exact: Hlo.
    have : c2 <= h2 by exact: Hhi.
    lia.
Qed.

(** *** Constant-divisor, congruence-pinned residue (multi-block).

    When the divisor is a nonzero constant [n] with [|n|] dividing the
    dividend's modulus [m2], every dividend value is congruent to [r2]
    modulo [|n|], so [Z.rem _ n] is *constant* across the whole dividend
    set as soon as the dividend has a single sign — even when it spans
    many quotient blocks (where [const_block] gives up). The result is
    the point interval at [rho = r2 mod |n|] (nonnegative dividend) or
    [rho = -((-r2) mod |n|)] (nonpositive dividend). Flagship example:
    [[0,100] ∩ (3 + 10ℤ)] rem [{10}] yields the point interval [[3,3]]. *)

Definition itv_nonnegb (i : interval) : bool :=
  match fst i with
  | WithTop.NotTop l => 0 <=? l
  | WithTop.Top => false
  end.

Definition itv_nonposb (i : interval) : bool :=
  match snd i with
  | WithTop.NotTop h => h <=? 0
  | WithTop.Top => false
  end.

Lemma itv_nonnegb_spec (i : interval) (c : Z) :
  itv_nonnegb i -> c ∈ γ[itv] i -> 0 <= c.
Proof.
  rewrite /itv_nonnegb. case: i => [[|l] h] //.
  move=> /Z.leb_le Hl [Hlo _].
  have : l <= c by exact: Hlo. lia.
Qed.

Lemma itv_nonposb_spec (i : interval) (c : Z) :
  itv_nonposb i -> c ∈ γ[itv] i -> c <= 0.
Proof.
  rewrite /itv_nonposb. case: i => [l [|h]] //.
  move=> /Z.leb_le Hh [_ Hhi].
  have : c <= h by exact: Hhi. lia.
Qed.

Definition const_residue (a2 a1 : collapsed_ad) : option Z :=
  match is_singleton a1 with
  | Some n =>
      if (n =? 0) || negb (snd (snd a2) mod Z.abs n =? 0) then None
      else if itv_nonnegb (fst a2) then Some (fst (snd a2) mod Z.abs n)
      else if itv_nonposb (fst a2) then Some (- ((- fst (snd a2)) mod Z.abs n))
      else None
  | None => None
  end.

(** What [const_residue] certifies: a nonzero constant divisor [n], and
    a *constant* remainder [rho] across the dividend's concretization. *)
Lemma const_residue_some (a2 a1 : collapsed_ad) (rho : Z) :
  const_residue a2 a1 = Some rho ->
  exists n : Z,
    n <> 0 /\
    (forall c1, c1 ∈ γ[collapsed_ad] a1 -> c1 = n) /\
    (forall c2, c2 ∈ γ[collapsed_ad] a2 -> Z.rem c2 n = rho).
Proof.
  case: a2 => [i2 [r2 m2]].
  rewrite /const_residue /=.
  case Hsg: (is_singleton a1) => [n|] //.
  case Hguard: ((n =? 0) || negb (m2 mod Z.abs n =? 0)) => //.
  move: Hguard
    => /Bool.orb_false_iff [/Z.eqb_neq Hn0 /Bool.negb_false_iff /Z.eqb_eq Hdiv].
  have HN : 0 < Z.abs n by lia.
  have [j Hj] := proj1 (Zmod_divides m2 (Z.abs n) ltac:(lia)) Hdiv.
  have HNdvd : (Z.abs n | m2) by rewrite Hj; apply Z.divide_factor_l.
  case Hnn: (itv_nonnegb i2).
  - move=> [= <-]. exists n.
    split; first exact: Hn0.
    split; first exact: is_singleton_sound a1 n Hsg.
    move=> c2 [Hc2i Hc2g].
    unfold_set in Hc2g.
    have Hc2nn : 0 <= c2 := itv_nonnegb_spec i2 c2 Hnn Hc2i.
    have [k Hk] : exists k, c2 - r2 = k * Z.abs n
      := Z.divide_trans _ _ _ HNdvd Hc2g.
    rewrite -(Z_rem_abs_r c2 n).
    rewrite (Zrem_Zmod_pos c2 (Z.abs n) Hc2nn HN).
    have -> : c2 = r2 + k * Z.abs n by lia.
    exact: Z_mod_plus_full.
  - case Hnp: (itv_nonposb i2) => // [= <-]. exists n.
    split; first exact: Hn0.
    split; first exact: is_singleton_sound a1 n Hsg.
    move=> c2 [Hc2i Hc2g].
    unfold_set in Hc2g.
    have Hc2np : c2 <= 0 := itv_nonposb_spec i2 c2 Hnp Hc2i.
    have [k Hk] : exists k, c2 - r2 = k * Z.abs n
      := Z.divide_trans _ _ _ HNdvd Hc2g.
    rewrite -(Z.opp_involutive c2) (Z.rem_opp_l _ _ Hn0).
    rewrite -(Z_rem_abs_r (- c2) n).
    rewrite (Zrem_Zmod_pos (- c2) (Z.abs n) ltac:(lia) HN).
    have -> : - c2 = - r2 + (- k) * Z.abs n by lia.
    by rewrite Z_mod_plus_full.
Qed.

(** On a [const_residue] input the collecting set is exactly the
    singleton [{rho}] (both operands being non-empty). *)
Lemma rem_collecting_const_residue (a2 a1 : collapsed_ad) (rho : Z) :
  const_residue a2 a1 = Some rho ->
  (exists c2, c2 ∈ γ[collapsed_ad] a2) ->
  (exists c1, c1 ∈ γ[collapsed_ad] a1) ->
  collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
    (γ[collapsed_ad] a2) (γ[collapsed_ad] a1)
  ⊆⊇ {[ x | x = rho ]}.
Proof.
  move=> Hcr [c20 Hc20] [c10 Hc10].
  have [n [Hn0 [Hconst Hrem]]] := const_residue_some a2 a1 rho Hcr.
  apply propset_equiv_iff => x. split.
  - move=> [c2 [c1 [Hc2 [Hc1 [_ Heq]]]]].
    have Hc1n := Hconst c1 Hc1. subst c1.
    apply/propset_elem_of_iff. rewrite -Heq.
    exact: Hrem.
  - move=> Hx. move/propset_elem_of_iff: Hx => ->.
    have Hc10n := Hconst c10 Hc10.
    exists c20, n.
    split; [exact: Hc20 | split; [by rewrite -Hc10n | split; [exact: Hn0 |]]].
    exact: Hrem.
Qed.

(** The point interval [[rho, rho]] is the best interval for the
    singleton [{rho}]. *)
Lemma itv_point_best (rho : Z) :
  BestAbstraction (A:=itv) (WithTop.NotTop rho, WithTop.NotTop rho)
    {[ x | x = rho ]}.
Proof.
  apply best_abstraction_iff; split.
  - move=> z Hz. move/propset_elem_of_iff: Hz => ->.
    apply/itv_gammaP.
    by rewrite /itv_gammab /glb_gammab /lub_gammab /= !Z.leb_refl.
  - move=> b Hb.
    have Hrho : rho ∈ γ[itv] b.
    { apply: Hb. by apply/propset_elem_of_iff. }
    case: b Hrho {Hb} => [[|lb] [|hb]] [Hlo Hhi]; apply/is_includedP => //=.
    + have Hh : rho <= hb by exact: Hhi.
      by apply/Z.leb_le.
    + have Hl : lb <= rho by exact: Hlo.
      by apply/andP; split; [apply/Z.leb_le |].
    + have Hl : lb <= rho by exact: Hlo.
      have Hh : rho <= hb by exact: Hhi.
      by apply/andP; split; apply/Z.leb_le.
Qed.

Definition rem_itv_envelope (a2 a1 : collapsed_ad) : interval :=
  match const_block a2 a1 with
  | Some (n, q) => itv_add_const (- (n * q)) (fst a2)
  | None => if narrow_divb a2 a1 then fst a2
            else match const_residue a2 a1 with
                 | Some rho => (WithTop.NotTop rho, WithTop.NotTop rho)
                 | None => (WithTop.Top, WithTop.Top)
                 end
  end.

(** Soundness of the envelope for *all* inputs. On the [const_block]
    branch it is the precise shifted interval; on the [narrow_divb] branch
    [Z.rem] is the identity and the envelope is the dividend's interval;
    otherwise the top interval. *)
Lemma rem_itv_envelope_sound (a2 a1 : collapsed_ad) :
  Overapproximates (A:=itv) (rem_itv_envelope a2 a1)
    (collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
       (γ[collapsed_ad] a2) (γ[collapsed_ad] a1)).
Proof.
  rewrite /rem_itv_envelope.
  case Hcb: (const_block a2 a1) => [[n q]|].
  - have [Hn [Hconst Hblock]] := const_block_some a2 a1 n q Hcb.
    move=> c [c2 [c1 [Hc2 [Hc1 [_ Heq]]]]].
    have Hc1n := Hconst c1 Hc1. subst c1.
    rewrite (Z_rem_quot_eq c2 n) (Hblock c2 Hc2) in Heq.
    apply/itv_add_const_gamma.
    have -> : c - - (n * q) = c2 by lia.
    exact: gamma_fst_itv a2 c2 Hc2.
  - case Hnb: (narrow_divb a2 a1).
    + have [_ Hnarrow] := narrow_divb_spec a2 a1 Hnb.
      move=> c [c2 [c1 [Hc2 [Hc1 [_ Heq]]]]].
      rewrite -Heq (Z_rem_small_abs c2 c1 (Hnarrow c2 Hc2 c1 Hc1)).
      exact: gamma_fst_itv a2 c2 Hc2.
    + case Hcr: (const_residue a2 a1) => [rho|].
      * have [n [Hn0 [Hconst Hrem]]] := const_residue_some a2 a1 rho Hcr.
        move=> c [c2 [c1 [Hc2 [Hc1 [_ Heq]]]]].
        rewrite -Heq (Hconst c1 Hc1) (Hrem c2 Hc2).
        apply/itv_gammaP.
        by rewrite /itv_gammab /glb_gammab /lub_gammab /= !Z.leb_refl.
      * move=> c _. apply/itv_gammaP. by [].
Qed.

(** On the [narrow_divb] branch the envelope is the *best* interval, by
    [rem_itv_identity_best]. *)
Lemma rem_itv_envelope_narrow_best (a2 a1 : collapsed_ad) :
  const_block a2 a1 = None ->
  narrow_divb a2 a1 ->
  MaximallyReduced a2 ->
  (exists c2, c2 ∈ γ[collapsed_ad] a2) ->
  (exists c1, c1 ∈ γ[collapsed_ad] a1) ->
  BestAbstraction (A:=itv) (rem_itv_envelope a2 a1)
    (collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
       (γ[collapsed_ad] a2) (γ[collapsed_ad] a1)).
Proof.
  move=> Hcb Hnb Hred Hne2 [c1 Hc1].
  have [Hnz Hnarrow] := narrow_divb_spec a2 a1 Hnb.
  rewrite /rem_itv_envelope Hcb Hnb.
  apply: rem_itv_identity_best => //.
  - by exists c1; split; [ | exact: Hnz].
  - move=> c2 Hc2 d1 Hd1 _. exact: Hnarrow.
Qed.

(** On the [const_residue] branch the envelope is the *best* interval:
    the collecting set is exactly the singleton [{rho}], and the point
    interval is its best abstraction. No maximal-reduction hypothesis on
    the operands is needed. *)
Lemma rem_itv_envelope_const_residue_best (a2 a1 : collapsed_ad) (rho : Z) :
  const_block a2 a1 = None ->
  narrow_divb a2 a1 = false ->
  const_residue a2 a1 = Some rho ->
  (exists c2, c2 ∈ γ[collapsed_ad] a2) ->
  (exists c1, c1 ∈ γ[collapsed_ad] a1) ->
  BestAbstraction (A:=itv) (rem_itv_envelope a2 a1)
    (collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
       (γ[collapsed_ad] a2) (γ[collapsed_ad] a1)).
Proof.
  move=> Hcb Hnb Hcr Hne2 Hne1.
  rewrite /rem_itv_envelope Hcb Hnb Hcr.
  apply: (best_abstraction_equiv (A:=itv)
            (WithTop.NotTop rho, WithTop.NotTop rho) _ _ (itv_point_best rho)).
  symmetry.
  exact: rem_collecting_const_residue Hcr Hne2 Hne1.
Qed.

(** Flagship: the dividend [[0,100] ∩ (3 + 10ℤ)] with the constant
    divisor [{10}] produces the point interval [[3,3]]. [const_block]
    rejects this input (the dividend spans eleven quotient blocks); the
    congruence pins the residue. Together with [rem_cong] (which yields
    [(3, 10)] here) the reduced result concretizes to [{3}]. *)
Example rem_itv_envelope_flagship :
  rem_itv_envelope ((WithTop.NotTop 0, WithTop.NotTop 100), (3, 10))
                   ((WithTop.NotTop 10, WithTop.NotTop 10), (10, 0))
  = (WithTop.NotTop 3, WithTop.NotTop 3).
Proof. by vm_compute. Qed.

(** On the [const_block] branch the envelope is the *best* interval, by
    [rem_itv_const_block_best]. *)
Lemma rem_itv_envelope_const_block_best (a2 a1 : collapsed_ad) (n q : Z) :
  const_block a2 a1 = Some (n, q) ->
  MaximallyReduced a2 ->
  (exists c2, c2 ∈ γ[collapsed_ad] a2) ->
  (exists c1, c1 ∈ γ[collapsed_ad] a1) ->
  BestAbstraction (A:=itv) (rem_itv_envelope a2 a1)
    (collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
       (γ[collapsed_ad] a2) (γ[collapsed_ad] a1)).
Proof.
  move=> Hcb Hred Hne2 Hne1.
  have [Hn [Hconst Hblock]] := const_block_some a2 a1 n q Hcb.
  rewrite /rem_itv_envelope Hcb.
  exact: rem_itv_const_block_best a2 a1 n q Hred Hne2 Hn Hne1 Hconst Hblock.
Qed.

Definition rem_itv (a2 a1 : collapsed_ad) : WithBottom.with_bottom interval :=
  if is_bottomb a2 || is_bottomb a1 || divisor_trivialb a1
  then WithBottom.Bot
  else WithBottom.NotBot (rem_itv_envelope a2 a1).

(** The collecting [Z.rem] set is empty whenever the [Bot] dispatch
    condition holds. *)
Lemma rem_collecting_empty (a2 a1 : collapsed_ad) :
  is_bottomb a2 || is_bottomb a1 || divisor_trivialb a1 ->
  forall c, c ∈ collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
                 (γ[collapsed_ad] a2) (γ[collapsed_ad] a1) -> False.
Proof.
  move=> Hcond c [c2 [c1 [Hc2 [Hc1 [Hc1ne Heq]]]]].
  move: Hcond => /orP [/orP [Hb | Hb] | Ht].
  - move/is_bottombP: Hb => Hbot.
    have := proj1 (is_bottom_gamma_empty a2 Hbot) c2 Hc2. by [].
  - move/is_bottombP: Hb => Hbot.
    have := proj1 (is_bottom_gamma_empty a1 Hbot) c1 Hc1. by [].
  - apply: Hc1ne. exact: divisor_trivial_empty a1 Ht c1 Hc1.
Qed.

(** Soundness of [rem_itv]: holds for all inputs. On the [NotBot] branch
    it delegates to [rem_itv_envelope_sound], which is precise on the
    [const_block] case and the top interval otherwise. *)
Lemma rem_itv_sound (a2 a1 : collapsed_ad) :
  Overapproximates (A:=WithBottom.ad itv) (rem_itv a2 a1)
    (collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
       (γ[collapsed_ad] a2) (γ[collapsed_ad] a1)).
Proof.
  move=> c Hc. rewrite /rem_itv.
  case Hcond: (is_bottomb a2 || is_bottomb a1 || divisor_trivialb a1).
  - exfalso. exact: rem_collecting_empty a2 a1 Hcond c Hc.
  - change (c ∈ γ[itv] (rem_itv_envelope a2 a1)).
    exact: rem_itv_envelope_sound a2 a1 c Hc.
Qed.

(** Optimality, empty branch: [Bot] is the best abstraction whenever the
    dispatch condition holds. *)
Lemma rem_itv_bot_best (a2 a1 : collapsed_ad) :
  is_bottomb a2 || is_bottomb a1 || divisor_trivialb a1 ->
  BestAbstraction (A:=WithBottom.ad itv) WithBottom.Bot
    (collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
       (γ[collapsed_ad] a2) (γ[collapsed_ad] a1)).
Proof.
  move=> Hcond. apply: WithBottom.BestAbstraction_Bot.
  exact: rem_collecting_empty a2 a1 Hcond.
Qed.

(** ** [rem] on the convention-compliant signature.

    Per the transfer-function convention, [rem] takes *non-bottom*
    arguments ([non_bottom_zic]) and returns a *bottom-carrying* result
    ([zic]), because [rem] of two non-empty sets can still be empty
    — namely when the divisor concretizes to [{0}] (no valid divisor
    under the partial [d <> 0] semantics).

    With non-bottom arguments the empty-result condition collapses to a
    single test: the [is_bottomb a2 || is_bottomb a1] cases of the old
    [collapsed_ad]-typed [rem_itv] cannot arise. So the only dispatch is
    [divisor_trivialb_nb]; otherwise we land a raw result into [zic]
    via [reduce_final].

    PRECISION STATUS: the bottom branch is exact. On the non-bottom
    branch the interval is now [rem_itv_envelope], which is *best* on the
    constant-divisor single-block case ([const_block] /
    [rem_itv_envelope_const_block_best]) and the top interval otherwise;
    the congruence is still the placeholder [(0,1)] (= ℤ). Remaining
    precision work: the general interval envelope, and a real [rem_cong]. *)

(** Divisor-trivial test for non-bottom arguments: no [is_bottomb] case
    (the argument is structurally non-empty). *)
Definition divisor_trivialb_nb (a1 : prod_ajsl) : bool :=
  match fst a1 with
  | (WithTop.NotTop l, WithTop.NotTop h) => (l =? 0) && (h =? 0)
  | _ => false
  end.

Lemma divisor_trivial_nb_empty (a1 : prod_ajsl) :
  divisor_trivialb_nb a1 -> forall c1, c1 ∈ γ[prod_ajsl] a1 -> c1 = 0.
Proof.
  rewrite /divisor_trivialb_nb.
  case: a1 => [[l h] c]. rewrite /fst.
  case: l => [|lz] //; case: h => [|hz] //.
  move=> /andP [/Z.eqb_eq -> /Z.eqb_eq ->] c1 [Hc1i _].
  move/itv_gammaP: Hc1i.
  rewrite /itv_gammab /glb_gammab /lub_gammab => /andP [Hle Hge].
  move: Hle Hge => /Z.leb_le ? /Z.leb_le ?. lia.
Qed.

(** Projection of a [non_bottom_zic] element to its raw [prod_ajsl]
    carrier (through the two [Subset] layers). The pattern match forces
    the [abs_car]/[ad_car] reductions a bare backtick leaves stuck. *)
Definition rd_car (a : non_bottom_zic) : prod_ajsl :=
  match a with exist _ (exist _ a0 _) _ => a0 end.

(** γ passes through the two [Subset] layers unchanged: the concretization
    of a [non_bottom_zic] is that of its raw carrier. (Holds by reduction
    once [a] is exposed as an [exist].) *)
Lemma nb_gamma (a : non_bottom_zic) :
  γ[non_bottom_zic] a = γ[collapsed_ad] (rd_car a).
Proof. by case: a => [[a0 p0] p]. Qed.

(** *** Result congruence.

    Algebraic fact (sign-independent, arbitrary divisor): writing the
    dividend congruence [(r2, m2)] and the divisor congruence [(r1, m1)],

      [Z.rem c2 c1 ≡ r2  (mod gcd m2 (gcd r1 m1))].

    Indeed [Z.rem c2 c1 = c2 - c1 * Z.quot c2 c1]; the modulus divides
    [m2], hence [c2 ≡ r2]; and it divides [gcd r1 m1], hence every divisor
    value [c1 = r1 + k*m1], hence the subtracted multiple. This yields a
    *sound* result congruence for every input pair (the argument does not
    even need [c1 <> 0]), replacing the old placeholder [(0,1)]. When
    [gcd m2 (gcd r1 m1) = 1] the result congruence is all of ℤ — which is
    then genuinely the most precise congruence, not a loss. *)

Definition rem_cong (g2 g1 : Z * Z) : Z * Z :=
  let '(r2, m2) := g2 in
  let '(r1, m1) := g1 in
  (r2, Z.gcd m2 (Z.gcd r1 m1)).

(** The flagship dividend [≡ 3 (mod 10)] with divisor the constant [10]
    (as a congruence, [(10, 0)]): the result congruence is [≡ 3 (mod 10)],
    since [gcd(10, gcd(10, 0)) = 10]. *)
Example rem_cong_flagship : rem_cong (3, 10) (10, 0) = (3, 10).
Proof. by vm_compute. Qed.

Lemma rem_cong_divide (r2 m2 r1 m1 c2 c1 : Z) :
  (m2 | c2 - r2) -> (m1 | c1 - r1) ->
  (Z.gcd m2 (Z.gcd r1 m1) | Z.rem c2 c1 - r2).
Proof.
  move=> [k2 Hk2] [k1 Hk1].
  have Hg_m2 : (Z.gcd m2 (Z.gcd r1 m1) | m2) := Z.gcd_divide_l _ _.
  have Hg_r1 : (Z.gcd m2 (Z.gcd r1 m1) | r1).
  { apply: (Z.divide_trans _ (Z.gcd r1 m1)).
    - exact: Z.gcd_divide_r.
    - exact: Z.gcd_divide_l. }
  have Hg_m1 : (Z.gcd m2 (Z.gcd r1 m1) | m1).
  { apply: (Z.divide_trans _ (Z.gcd r1 m1)).
    - exact: Z.gcd_divide_r.
    - exact: Z.gcd_divide_r. }
  have -> : Z.rem c2 c1 - r2 = k2 * m2 - c1 * Z.quot c2 c1
    by rewrite Z_rem_quot_eq; lia.
  apply: Z.divide_sub_r.
  - by apply: Z.divide_mul_r.
  - apply: Z.divide_mul_l.
    have -> : c1 = r1 + k1 * m1 by lia.
    apply: Z.divide_add_r => //.
    by apply: Z.divide_mul_r.
Qed.

(** Soundness of the result congruence, at the product level: for any
    concrete pair drawn from the operands' concretizations, the remainder
    lies in the class computed by [rem_cong]. *)
Lemma rem_cong_sound (a2 a1 : collapsed_ad) (c2 c1 : Z) :
  c2 ∈ γ[collapsed_ad] a2 -> c1 ∈ γ[collapsed_ad] a1 ->
  Z.rem c2 c1 ∈ γ[cong_ad] (rem_cong (snd a2) (snd a1)).
Proof.
  case: a2 => [i2 [r2 m2]]; case: a1 => [i1 [r1 m1]].
  move=> [_ Hc2] [_ Hc1] /=.
  unfold_set in Hc2. unfold_set in Hc1. unfold_set.
  exact: rem_cong_divide.
Qed.

(** Raw (unreduced) result. The interval is [rem_itv_envelope] — best on
    the constant-divisor single-block, narrow-dividend, and
    congruence-pinned-residue cases, the top interval otherwise. The
    congruence is [rem_cong] — sound on all inputs. *)
Definition rem_raw (a2 a1 : prod_ajsl) : prod_ajsl :=
  (rem_itv_envelope a2 a1, rem_cong (snd a2) (snd a1)).

Definition rem_final (x y : non_bottom_zic) : zic :=
  if divisor_trivialb_nb (rd_car y)
  then bottom_final
  else reduce_final (rem_raw (rd_car x) (rd_car y)).

(** With non-bottom arguments, the collecting [Z.rem] set is empty
    exactly when the divisor is trivial. *)
Lemma rem_final_empty (x y : non_bottom_zic) :
  divisor_trivialb_nb (rd_car y) ->
  forall c, c ∈ collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
                 (γ[non_bottom_zic] x) (γ[non_bottom_zic] y) -> False.
Proof.
  move=> Ht c [c2 [c1 [_ [Hc1 [Hc1ne _]]]]].
  apply: Hc1ne. move: Ht Hc1. case: y => [[ay py] my] Ht Hc1.
  exact: (divisor_trivial_nb_empty ay Ht c1 Hc1).
Qed.

Lemma rem_final_sound (x y : non_bottom_zic) :
  Overapproximates (A:=zic) (rem_final x y)
    (collecting_binary_forward_partial (fun _ d => d <> 0) Z.rem
       (γ[non_bottom_zic] x) (γ[non_bottom_zic] y)).
Proof.
  move=> c Hc. rewrite /rem_final.
  case Hcond: (divisor_trivialb_nb (rd_car y)).
  - exfalso. exact: rem_final_empty x y Hcond c Hc.
  - have [_ Hsub] := reduce_final_gamma (rem_raw (rd_car x) (rd_car y)).
    apply: (Hsub c). split.
    + rewrite !nb_gamma in Hc.
      exact: rem_itv_envelope_sound (rd_car x) (rd_car y) c Hc.
    + rewrite !nb_gamma in Hc.
      move: Hc => [c2 [c1 [Hc2 [Hc1 [_ Heq]]]]].
      rewrite -Heq.
      exact: rem_cong_sound (rd_car x) (rd_car y) c2 c1 Hc2 Hc1.
Qed.
