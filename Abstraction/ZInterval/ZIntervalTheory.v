(* ZIntervalTheory.v - Interval arithmetic for integers *)
(* Noth: there are intervals in mathcomp; we could reuse their notations. *)

(* STATUS (ladder: sound < best < exact < α-complete).

   All transfer functions now live in Transfer_function/ZInterval/; what is
   left here is the abstraction itself, the generic α-machinery the operation
   proofs share, and the [classify] inversion lemmas.
     opp:  exact                      -- OppTheory.v
     add:  sound + best (α-complete)  -- AddTheory.v
     sub:  sound + exact (non-bottom) -- AddTheory.v
     backward add/sub: exact          -- AddBackwardTheory.v
     backward mul:  sound             -- MulBackwardTheory.v
     quot: best, all 9 sign cases     -- QuotTheory.v
     mul:  sound + best (α-complete)  -- MulTheory.v
     leb:  exact                      -- LeTheory.v
     eqb:  exact                      -- EqbTheory.v

   NOTE: this file still bundles the computational core of the abstraction
   (the extractable lattice/bound definitions) and its mathematical theory.
   The Comp/Theory split prescribed by architecture.org is deferred. *)

Require Import Abstraction AbstractLattice.
Require Import ssreflect ssrbool ssrfun.
Require Import BoundAbstraction.
Require Import AbstractionCombination.
Require Import BoundLattice.
Require Import autoreflect.
Require Import Tactics.
Require Import Stdlib.Bool.Bool.
Require Import Quadrivalent.
Require Import ZInterval.
(* From Hammer Require Import Hammer. *)
From Stdlib Require Import Lia. (* lia/nia; avoid Psatz which loads Reals axioms *)
Require Import Stdlib.ZArith.ZArith.
Open Scope Z_scope.             (* Arithmetic operations are all on Z; avoids %Z everywhere. *)
Generalizable All Variables.

Open Scope signature_scope.

From Stdlib Require Export Setoid.
From Stdlib Require Export Classes.Morphisms.
From Stdlib Require Export Morphisms.


Declare Scope interval_scope.
Local Open Scope interval_scope.

(* Maybe not needed. *)
(* From Stdlib Require Import Logic.ProofIrrelevance. *)

(* Strategy: do the proofs on the more general case where we have
   markers for infinity, on the bottom and non-bottom cases.

   From that, we can extract specific proofs when we only have finite
   intervals, and better implementations when Z is positive.

   I should start with the best abstraction proof, as it is useful
   after this.  *)

(* We use two representations:
   - One where Z (and le) is extended with -Inf and +Inf. Used only in proofs.
   - One using option Z, used for representation in the interval.
     This will in particular avoid a lot of case splitting. *)

(** * Definitions, core abstraction. *)

Lemma z_cl_equiv_spec a1 a2: Z.eq a1 a2 <-> Z.le a1 a2 /\ Z.le a2 a1.
Proof.
  unfold Z.eq; split.
  - move => ->; split; reflexivity.
  - move => [H1 H2]. apply Z.le_antisymm; assumption.
Qed.

(** Z forms a concrete lattice with Z.le, Z.min, Z.max. *)
Definition Z_CL : @ConcreteLattice Z :=
  @BuildConcreteLattice Z Z Z.le Z.eq Z.min Z.max
    Z.le_preorder z_cl_equiv_spec
    Z.le_min_l Z.le_min_r Z.min_glb
    Z.le_max_l Z.le_max_r Z.max_lub.

Section AD.
  Definition glb : abstract_lattice Z := GLB.al Z_CL.
  Definition lub : abstract_lattice Z := LUB.al Z_CL.
  Definition glbtop : abstract_lattice Z := GLBUnbounded.al Z_CL.
  Definition lubtop : abstract_lattice Z := LUBUnbounded.al Z_CL.
End AD.

(* Interval is the concrete datatype, and itv is the abstraction.  Be
   careful to use functions from/to intervals/nb_intervals for
   functions to be extracted (and not the coercion from itv/nb_itv);
   otherwise, the extraction is messy. *)
Definition itv : abstract_lattice Z := IntervalUnbounded.al Z_CL.

(** Intervals are convex: [γ[itv] i] contains every point lying between
    two of its members. Specialisation of [IntervalUnbounded.convex]. *)
Lemma itv_convex (i : interval) (a b c : Z) :
  a ∈ γ[itv] i -> b ∈ γ[itv] i -> a <= c <= b -> c ∈ γ[itv] i.
Proof. case: i => [[|l] [|h]]; unfold_set; simpl; lia. Qed.

Definition nbitv : abstract_domain Z := NonEmpty.ad itv non_bottom.

Lemma gamma_nbitv_gamma_itv c i: c ∈ γ[nbitv] i <-> c ∈ γ[itv] (`i).
Proof.
  move: i => [[[|l] [|h]] P] //=.
Qed.

(** Set-level form of [gamma_nbitv_gamma_itv], for rewriting a whole
    concretization (rather than a membership) when transporting a result
    proved on [nbitv] down to the raw carrier. *)
Lemma gamma_nbitv_gamma_itv_set (i : nb_interval) : γ[nbitv] i ⊆⊇ γ[itv] (`i).
Proof. split=> c; by rewrite gamma_nbitv_gamma_itv. Qed.



Instance glb_gammaP: forall l z, AutoReflect(z ∈ γ[glb] l)(ZInterval.glb_gammab l z).
Proof. apply/Z.leb_spec0. Qed.

Instance lub_gammaP: forall l z, AutoReflect(z ∈ γ[lub] l)(ZInterval.lub_gammab l z).
Proof. move => l z. apply/Z.leb_spec0. Qed.



Instance itv_gammaP i z: AutoReflect(z ∈ γ[itv] i)(itv_gammab i z).
Proof.
  eassert(forall i, AutoReflect(z ∈ γ[glb] i)(_)) by apply _.
  eassert(forall l, AutoReflect(z ∈ γ[glbtop] l)(_)) by apply _.
  eassert(forall i, AutoReflect(z ∈ γ[lub] i)(_)) by apply _.
  eassert(forall l, AutoReflect(z ∈ γ[lubtop] l)(_)) by apply _.
  eassert(forall i, AutoReflect(z ∈ γ[itv] i)(_)) by apply _.
  apply _.
Qed.


(** On non-bottom intervals, the low and high properties are independent. *)
Lemma nbitv_gammaE c i:
  c ∈ γ[nbitv] i <-> let (l,h) := `i in c ∈ γ[glbtop] (l) /\ c ∈ γ[lubtop] (h).
Proof.
  move: i => [[l h] P]. done.
Qed.

(** Reading one bound off a γ-membership.  The other bound may be [Top], and
    these never look at it — which is what keeps the arithmetic in the transfer
    function proofs free of case splits on bounds they do not use. *)
Lemma gamma_itv_low (l : Z) (h : WithTop.with_top Z) c :
  c ∈ γ[itv] (WithTop.NotTop l, h) -> l <= c.
Proof. by move=> [Hl _]; unfold_set in Hl. Qed.

Lemma gamma_itv_high (l : WithTop.with_top Z) (h : Z) c :
  c ∈ γ[itv] (l, WithTop.NotTop h) -> c <= h.
Proof. by move=> [_ Hh]; unfold_set in Hh. Qed.

(** Exact order. *)

Global Instance z_leP (z2 z1:Z): (AutoReflect(z2 <= z1)(Z.leb z2 z1)).
Proof. apply Z.leb_spec0. Qed.

Global Instance glbtop_is_includedP a2 a1 :
  AutoReflect(a2 ⊑[glbtop] a1)(ZInterval.glbtop_is_includedb a2 a1).
Proof.
  { apply WithTop.is_includedP. apply _. }
Qed.

Global Instance lubtop_is_includedP a2 a1 :
  AutoReflect(a2 ⊑[lubtop] a1)(ZInterval.lubtop_is_includedb a2 a1).
Proof.
{ apply WithTop.is_includedP. apply _. }
Qed.

Global Instance is_includedP a2 a1:
  (AutoReflect(a2 ⊑[itv] a1)(ZInterval.is_included a2 a1)).
Proof.
  move:a2 => [l2 h2].
  move:a1 => [l1 h1].
  apply Conjunction.is_includedP.
  apply glbtop_is_includedP.
  apply lubtop_is_includedP.
Qed.

(** * Stability of the interval domain.

    Interval [⊑] and γ-membership are decidable (the reflections
    above), hence [¬¬]-stable; and [IsAlpha (A:=itv) …], being a
    [∀/↔/→] of those, is stable too. This lets α-completeness proofs
    extract membership witnesses through the [¬¬]-monad, with no
    decidable-membership hypothesis on the abstracted set. *)
Global Instance itv_le_stable (a b : interval) : Stable (a ⊑[itv] b) :=
  dec_stable (decP (is_includedP a b)).

Global Instance itv_gamma_stable (c : Z) (a : interval) :
  Stable (c ∈ γ[itv] a) :=
  dec_stable (decP (itv_gammaP a c)).

Global Instance is_alpha_itv_stable (αS : interval) (S : ℘ Z) :
  Stable (IsAlpha (A:=itv) αS S).
Proof.
  (* [IsAlpha] unfolds to [∀a, S ⊆ γ a ↔ αS ⊑ a]; typeclass resolution
     assembles stability from [stable_forall]/[stable_iff]/[stable_impl]
     and the [itv_le_stable]/[itv_gamma_stable] leaves. *)
  rewrite /IsAlpha. exact _.
Qed.

(** Leaf [Stable] instances for the [glbtop] / [lubtop] components, so
    that [Stable (IsAlpha (A:=glbtop) …)] / [(A:=lubtop) …] can be
    assembled by typeclass resolution in the same way. *)
Global Instance glbtop_le_stable (a b : WithTop.with_top Z) :
  Stable (a ⊑[glbtop] b) :=
  dec_stable (decP (glbtop_is_includedP a b)).

Global Instance lubtop_le_stable (a b : WithTop.with_top Z) :
  Stable (a ⊑[lubtop] b) :=
  dec_stable (decP (lubtop_is_includedP a b)).

Global Instance glbtop_gamma_stable (c : Z) (a : WithTop.with_top Z) :
  Stable (c ∈ γ[glbtop] a).
Proof.
  case: a => [|x] /=.
  - by unfold_set => _; trivial.
  - exact: (dec_stable (decP (glb_gammaP x c))).
Qed.

Global Instance lubtop_gamma_stable (c : Z) (a : WithTop.with_top Z) :
  Stable (c ∈ γ[lubtop] a).
Proof.
  case: a => [|x] /=.
  - by unfold_set => _; trivial.
  - exact: (dec_stable (decP (lub_gammaP x c))).
Qed.

Global Instance is_alpha_glbtop_stable (α : WithTop.with_top Z) (S : ℘ Z) :
  Stable (IsAlpha (A:=glbtop) α S).
Proof. rewrite /IsAlpha. exact _. Qed.

Global Instance is_alpha_lubtop_stable (α : WithTop.with_top Z) (S : ℘ Z) :
  Stable (IsAlpha (A:=lubtop) α S).
Proof. rewrite /IsAlpha. exact _. Qed.

(** Expose [cl_le Z_CL] as [Z.le] so [unfold_set] descends through the
    [ConcreteLattice] abstraction and [lia]/[nia] see the concrete relation. *)
Global Instance unfold_set_cl_le_Z (a b : Z) :
  UnfoldSet (cl_le Z_CL a b) (a <= b)%Z.
Proof. constructor; rewrite /cl_le /=; tauto. Qed.

(** Constructive Markov-style reverse of [no_upper_bound_implies_top_is_best]
    on [Z]: from [IsAlpha Top S], we cannot constructively extract a witness
    above [M], but we can derive its [~~] form. Z totality
    ([Z.le_gt_cases]) is the only classical-flavoured step. *)
Lemma is_alpha_lubtop_top_nn (S : ℘ Z) (M : Z) :
  IsAlpha (A:=lubtop) WithTop.Top S ->
  ~ ~ (exists c, c ∈ S /\ M < c).
Proof.
  move=> Ha Hnex.
  have Hnotsub: ~ (S ⊆ γ[lubtop] (WithTop.NotTop M)).
  { move=> Hsub. exact: (proj1 (Ha (WithTop.NotTop M)) Hsub). }
  apply: Hnotsub => c Hc.
  destruct (Z.le_gt_cases c M) as [Hle | Hgt].
  - exact Hle.
  - exfalso. apply: Hnex. by exists c; split; [exact Hc | exact Hgt].
Qed.

(** CPS wrapper of [is_alpha_lubtop_top_nn]: extract the witness through any
    [Stable] continuation. *)
Lemma is_alpha_lubtop_top_witness {G : Prop} `{Stable G}
      (S : ℘ Z) (M : Z) :
  IsAlpha (A:=lubtop) WithTop.Top S ->
  ((exists c, c ∈ S /\ M < c) -> G) -> G.
Proof.
  move=> Ha Hk. apply: stable => Hng.
  apply: (is_alpha_lubtop_top_nn S M Ha) => Hex.
  exact: (Hng (Hk Hex)).
Qed.

(** [glbtop] dual of [is_alpha_lubtop_top_nn]: from [IsAlpha Top S]
    (S unbounded below), the [~~] form of "an element below M". *)
Lemma is_alpha_glbtop_top_nn (S : ℘ Z) (M : Z) :
  IsAlpha (A:=glbtop) WithTop.Top S ->
  ~ ~ (exists c, c ∈ S /\ c < M).
Proof.
  move=> Ha Hnex.
  have Hnotsub: ~ (S ⊆ γ[glbtop] (WithTop.NotTop M)).
  { move=> Hsub. exact: (proj1 (Ha (WithTop.NotTop M)) Hsub). }
  apply: Hnotsub => c Hc.
  destruct (Z.le_gt_cases M c) as [Hle | Hgt].
  - exact Hle.
  - exfalso. apply: Hnex. by exists c; split; [exact Hc | exact Hgt].
Qed.

Lemma is_alpha_glbtop_top_witness {G : Prop} `{Stable G}
      (S : ℘ Z) (M : Z) :
  IsAlpha (A:=glbtop) WithTop.Top S ->
  ((exists c, c ∈ S /\ c < M) -> G) -> G.
Proof.
  move=> Ha Hk. apply: stable => Hng.
  apply: (is_alpha_glbtop_top_nn S M Ha) => Hex.
  exact: (Hng (Hk Hex)).
Qed.


Lemma z_is_unbounded : forall a : Z, exists a' : Z, a' <= a /\ ~ (a' = a).
Proof.
  move=>a. exists (a-1). lia.
Qed.

Lemma z_is_unbounded_up : forall a : Z, exists a' : Z, a <= a' /\ ~ (a' = a).
Proof.
  move=>a. exists (a+1). lia.
Qed.

Lemma z_le_antisymm: Antisymmetric Z (=) Z.le.
Proof. apply _. Qed.


(** ExactOrder for non-empty Z intervals: instantiate the generic
    IntervalUnbounded lemma with Z's unboundedness and antisymmetry. *)
Instance IntervalUnbounded_ExactOrder: ExactOrder nbitv :=
  IntervalUnbounded.nonempty_exact_order Z_CL 0
    (GLBUnbounded.glbunbounded_is_included_exact
       Z.le z_is_unbounded z_le_antisymm)
    (LUBUnbounded.lubunbounded_is_included_exact
       Z.le z_is_unbounded_up z_le_antisymm).


(** * Galois connections. *)

Instance is_alpha_glb: StrongAlphaRelation glb := BoundAbstraction.GLB.galois Z.le.
Instance is_alpha_lub: StrongAlphaRelation lub := BoundAbstraction.LUB.galois Z.le.

Instance is_alpha_glbtop: WeakAlphaRelation glbtop := BoundAbstraction.GLBUnbounded.galoisW Z.le z_is_unbounded z_le_antisymm.
Program Instance is_alpha_lubtop: WeakAlphaRelation lubtop := BoundAbstraction.LUBUnbounded.galoisW Z.le _ _.
Next Obligation.
  unfold CRelationClasses.flip. exists (a+1). lia.
Qed.

Instance galoisW : WeakAlphaRelation itv := AbstractionCombination.Conjunction.galoisW glbtop lubtop is_alpha_glbtop is_alpha_lubtop.

(** Strong α relation for [lubtop] on [Z]: a true biconditional with
    [IsAlpha], obtained by carrying the classical content of the [Top] case
    inside the relation itself (per-[M] [~~] witness). The [NotTop] case
    matches the weak relation. The weak instance [is_alpha_lubtop] is kept
    around because constructing an [IsAlpha Top S] is easier via
    [no_upper_bound] (no [~~]); the strong instance is for *consuming* an
    [IsAlpha Top]. *)
Definition lubtop_strong_α (αS : lubtop) (S : ℘ Z) : Prop :=
  match αS with
  | WithTop.NotTop a => LUB.is_lub Z.le a S
  | WithTop.Top => forall M, ~ ~ (exists c, c ∈ S /\ M < c)
  end.

Lemma lubtop_strong_α_iff (a : lubtop) (S : ℘ Z) :
  lubtop_strong_α a S <-> IsAlpha (A:=lubtop) a S.
Proof.
  case: a => [|a] /=.
  - (* Top *)
    split.
    + move=> Hwit b; case: b => [|M] /=.
      * by unfold_set; split.
      * unfold_set; split; [|by []].
        move=> Hsub. apply: (Hwit M) => [[c [Hcin Hcgt]]].
        have Hle := Hsub _ Hcin. unfold_set in Hle. lia.
    + move=> Ha M. exact: is_alpha_lubtop_top_nn.
  - (* NotTop *)
    split.
    + (* LUB.is_lub a S → IsAlpha (NotTop a) S *)
      move=> Hlub.
      apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_lubtop) (WithTop.NotTop a) S).
      exact Hlub.
    + exact: (IsAlpha_lubtop_NotTop_is_lub Z.le a S).
Qed.

Program Instance lubtop_strong : StrongAlphaRelation lubtop :=
  { strong_α_relation := lubtop_strong_α }.
Next Obligation. exact: lubtop_strong_α_iff. Qed.

(** Witness that the strong instance unlocks no-best-abstraction proofs:
    a bounded set cannot have [Top] as its best abstraction. The weak
    instance is insufficient for this — only the biconditional reduces
    [~ IsAlpha Top S] to a constructive "S is bounded above" claim. *)
Example lubtop_top_not_best_for_bounded :
  ~ IsAlpha (A:=lubtop) WithTop.Top {[ z : Z | -10 <= z <= 10 ]}.
Proof.
  rewrite -lubtop_strong_α_iff /=.
  move=> Hwit. apply: (Hwit 10) => [[c [Hcin Hcgt]]].
  unfold_set in Hcin. lia.
Qed.


Global Instance itv_join_is_lub : JoinIsLUB itv :=
  IntervalUnbounded.IntervalUnbounded_JoinIsLUB Z_CL.

(** ** Meet.

    [ZInterval.meet] is *exact*: it concretizes to the intersection. Contrast with the
    join, which only over-approximates the union.

    In calculational derivations, it allows turns the [∩] introduced by inverting the
    operation into an abstract operation without loss of precision. *)

Lemma itv_meet_eq_al_meet (i1 i2 : interval) : ZInterval.meet i1 i2 = i1 ⊓[itv] i2.
Proof. by move: i1 i2 => [[|l1] [|h1]] [[|l2] [|h2]]. Qed.

(** The join counterpart, so that the computational [ZInterval.join] can be
    handed to any lemma stated on the lattice's ⊔ — [join_sound],
    [join_lub], [is_alpha_join_split]. *)
Lemma itv_join_eq_al_join (i1 i2 : interval) : ZInterval.join i1 i2 = i1 ⊔[itv] i2.
Proof. by move: i1 i2 => [[|l1] [|h1]] [[|l2] [|h2]]. Qed.

Lemma itv_meet_exact (i1 i2 : interval) :
  γ[itv] (ZInterval.meet i1 i2) ⊆⊇ γ[itv] i1 ∩ γ[itv] i2.
Proof.
  move: i1 i2 => [[|l1] [|h1]] [[|l2] [|h2]];
    unfold_set_equiv => c; unfold_set; simpl; lia.
Qed.

(** The same fact pointwise, as a view.  [itv_meet_exact] is the statement a
    calculational derivation wants; this is the one a proof *about a member*
    wants, and going through the set-level form costs a [proj1]/[proj2] and an
    [unfold_set] to take the [∩] apart again at every use.  With this, a
    hypothesis is taken apart by [move=> /itv_meetE [H1 H2]] and a goal is built
    by [apply/itv_meetE; split].

    TODO: this shape is under-used in the development and there are probably
    more of them worth naming. *)
Lemma itv_meetE (i1 i2 : interval) (c : Z) :
  c ∈ γ[itv] (ZInterval.meet i1 i2) <-> c ∈ γ[itv] i1 /\ c ∈ γ[itv] i2.
Proof.
  move: i1 i2 => [[|l1] [|h1]] [[|l2] [|h2]]; split; unfold_set; simpl; lia.
Qed.

(** The meet is a lower bound in the abstract order. *)
Lemma itv_meet_lower_bound_l (i1 i2 : interval) : ZInterval.meet i1 i2 ⊑[itv] i1.
Proof.
  apply/is_includedP.
  move: i1 i2 => [[|l1] [|h1]] [[|l2] [|h2]] //=;
    repeat (apply/andP; split=> //); apply/Z.leb_spec0; lia.
Qed.

(** ** Bound-level meet identities and clamps.

     Meeting an abstract bound with [Top] is the identity, but the or-pattern
     in [meet_lb]/[meet_ub] compiles to a match on the *first* argument, so it
     does not reduce on a variable bound.  These two lemmas make that
     reduction explicit.  [QuotBackwardTheory.v] used to carry them; they are
     carrier facts and belong here. *)
Lemma meet_lb_top_r (a : WithTop.with_top Z) : ZInterval.meet_lb a WithTop.Top = a.
Proof. by case: a. Qed.

Lemma meet_ub_top_r (a : WithTop.with_top Z) : ZInterval.meet_ub a WithTop.Top = a.
Proof. by case: a. Qed.

(** The specialised [clamp_*_bound] is exactly the generic [meet_lb] /
    [meet_ub] with a known concrete second argument.  This is the bridge
     from the efficient form to any lemma stated on [meet]. *)
Lemma clamp_lower_bound_meetE (k : Z) (b : WithTop.with_top Z) :
  ZInterval.clamp_lower_bound k b = ZInterval.meet_lb b (WithTop.NotTop k).
Proof. by case: b. Qed.

Lemma clamp_upper_bound_meetE (k : Z) (b : WithTop.with_top Z) :
  ZInterval.clamp_upper_bound k b = ZInterval.meet_ub b (WithTop.NotTop k).
Proof. by case: b. Qed.

(** ** Sign halves: the interval-level [strictly_negative_part] /
     [strictly_positive_part].

     The efficient form clamps only the relevant bound; the bridge back to
     the generic [meet] form is one rewrite.  The pointwise [γ] view is the
     one the backward quotient proofs use most. *)

Lemma itv_strictly_negative_part_meetE (i : interval) :
  ZInterval.itv_strictly_negative_part i =
  ZInterval.meet i (WithTop.Top, WithTop.NotTop (-1)).
Proof.
  move: i => [l h]. rewrite /ZInterval.itv_strictly_negative_part
    /ZInterval.meet /= meet_lb_top_r clamp_upper_bound_meetE. by case: h.
Qed.

Lemma itv_strictly_positive_part_meetE (i : interval) :
  ZInterval.itv_strictly_positive_part i =
  ZInterval.meet i (WithTop.NotTop 1, WithTop.Top).
Proof.
  move: i => [l h]. rewrite /ZInterval.itv_strictly_positive_part
    /ZInterval.meet /= meet_ub_top_r clamp_lower_bound_meetE. by case: l.
Qed.

Lemma itv_strictly_negative_partE (i : interval) (c : Z) :
  c ∈ γ[itv] (ZInterval.itv_strictly_negative_part i) <-> c ∈ γ[itv] i /\ c <= -1.
Proof.
  rewrite itv_strictly_negative_part_meetE itv_meetE.
  by split=> -[H1 H2]; split=> //; move: H2; unfold_set; simpl; lia.
Qed.

Lemma itv_strictly_positive_partE (i : interval) (c : Z) :
  c ∈ γ[itv] (ZInterval.itv_strictly_positive_part i) <-> c ∈ γ[itv] i /\ 1 <= c.
Proof.
  rewrite itv_strictly_positive_part_meetE itv_meetE.
  by split=> -[H1 H2]; split=> //; move: H2; unfold_set; simpl; lia.
Qed.

(** ** Absorbing a sign clamp into a meet.

     Clamping one operand of a meet changes nothing when the *other* operand
     is already clamped at least as tightly: [meet_lb] is a [Z.max], so a [1]
     already present on one side makes a [1] on the other side invisible.

     This is what makes the ∓1 clamp on the incoming divisor redundant in
     [interval_quot_solve_right_split] ([ZIntervalBackwardOps.v]) — the solve
     half it is met with is itself clamped off zero. It stops being redundant
     the moment the half carries a *better* bound than ∓1, which is what the
     congruence product's snapped divisor halves supply. *)
Lemma meet_lb_clamp_lower_absorb (k v : Z) (a : WithTop.with_top Z) :
  k <= v ->
  ZInterval.meet_lb (ZInterval.clamp_lower_bound k a) (WithTop.NotTop v)
  = ZInterval.meet_lb a (WithTop.NotTop v).
Proof. by case: a => [|z] /= H; f_equal; lia. Qed.

Lemma meet_ub_clamp_upper_absorb (k v : Z) (a : WithTop.with_top Z) :
  v <= k ->
  ZInterval.meet_ub (ZInterval.clamp_upper_bound k a) (WithTop.NotTop v)
  = ZInterval.meet_ub a (WithTop.NotTop v).
Proof. by case: a => [|z] /= H; f_equal; lia. Qed.

Lemma itv_meet_strictly_positive_part_absorb (i x : interval) (v : Z) :
  fst x = WithTop.NotTop v -> 1 <= v ->
  ZInterval.meet (ZInterval.itv_strictly_positive_part i) x = ZInterval.meet i x.
Proof.
  move: i x => [l h] [lx hx] /= -> Hv.
  by rewrite /ZInterval.meet /ZInterval.itv_strictly_positive_part /=
             (meet_lb_clamp_lower_absorb 1 v l Hv).
Qed.

Lemma itv_meet_strictly_negative_part_absorb (i x : interval) (v : Z) :
  snd x = WithTop.NotTop v -> v <= -1 ->
  ZInterval.meet (ZInterval.itv_strictly_negative_part i) x = ZInterval.meet i x.
Proof.
  move: i x => [l h] [lx hx] /= -> Hv.
  by rewrite /ZInterval.meet /ZInterval.itv_strictly_negative_part /=
             (meet_ub_clamp_upper_absorb (-1) v h Hv).
Qed.

(** ** Structural equality of intervals. *)

Lemma bound_equalP (a b : WithTop.with_top Z) : reflect (a = b) (ZInterval.bound_equal a b).
Proof.
  case: a => [|x]; case: b => [|y] /=; try by constructor.
  case: (Z.eqb_spec x y) => [->|Hne]; constructor=> //. by case.
Qed.

Lemma itv_equalP (i1 i2 : interval) : reflect (i1 = i2) (ZInterval.equiv i1 i2).
Proof.
  move: i1 i2 => [l1 h1] [l2 h2] /=.
  case: (bound_equalP l1 l2) => [->|Hl] /=; last by constructor => - [].
  case: (bound_equalP h1 h2) => [->|Hh] /=; first by constructor.
  by constructor => - [].
Qed.

(** ⊑ is antisymmetric on each bound abstraction, hence on [interval], with no
    side condition.  Nothing about [Z] is involved beyond [z_le_antisymm].

    Note that typeclass resolution has to go through the [abstract_lattice] →
    [abstract_domain] coercion and the [al]/[ad] definitions. For this, the
    idiom is to pass the hypotheses explicitly, as in [antisymmetry H1 H2].  A
    bare [apply: antisymmetry] on a goal [a = b] leaves the relation an evar,
    and resolution then searches every [Antisymmetric] instance in scope. *)
Global Instance glbtop_antisym : Antisymmetric glbtop (=) (⊑[glbtop]) :=
  GLBUnbounded.ad_antisymmetric Z.le (Hanti := z_le_antisymm).

Global Instance lubtop_antisym : Antisymmetric lubtop (=) (⊑[lubtop]) :=
  LUBUnbounded.ad_antisymmetric Z.le (Hanti := z_le_antisymm).

Global Instance itv_antisym : Antisymmetric itv (=) (⊑[itv]) :=
  IntervalUnbounded.ad_antisymmetric Z.le (Hanti := z_le_antisymm).

(** Non-bottom intervals: non_bottom is equivalent to non-empty concretization. *)
Lemma non_bottom_non_empty:
  forall i:interval, (non_bottom i) <->  exists c, c ∈ γ[itv] i.
Proof. exact (IntervalUnbounded.non_bottom_non_empty Z_CL 0). Qed.

(** An interval that abstracts a non-empty set is non-bottom: α-completeness
    makes γ contain the set ([gamma_alpha_extensive]), so any witness in the set
    is a witness in γ.  Spelled out once because the sign-split proofs need it
    for each half they produce. *)
Lemma non_bottom_of_alpha (i : interval) (S : ℘ Z) (c : Z) :
  IsAlpha (A:=itv) i S -> c ∈ S -> non_bottom i.
Proof.
  move=> Ha Hc; apply/non_bottom_non_empty.
  exists c; exact: (gamma_alpha_extensive itv _ _ Ha c Hc).
Qed.

(** A witness makes a set non-empty.  Spelled out because the codebase's
    non-emptiness hypotheses are existentials, while the sign split now hands
    back the actual extremal elements. *)
Lemma nonempty_of_mem {C : Type} (S : ℘ C) (c : C) : c ∈ S -> exists c', c' ∈ S.
Proof. by move=> Hc; exists c. Qed.

(** [ZInterval.join] preserves non-bottom: the union of two non-empty intervals is
    non-empty. (Used by the split-aware lattice check, where [join] is typed
    over the non-empty carrier and so must package an [nb_interval].) *)
Lemma itv_join_non_bottom (a b : interval) :
  non_bottom a -> non_bottom b -> non_bottom (ZInterval.join a b).
Proof.
  move=> /non_bottom_non_empty Ha _.
  apply/non_bottom_non_empty.
  exact: NonEmpty.nonempty_join_sound itv a b Ha.
Qed.

(** ** Collapsed-bottom intervals.

    The carrier [interval] has many syntactic representations of [∅]
    (any [(NotTop l, NotTop h)] with [l > h]). The [CollapsedBottom]
    combinator from [AbstractionCombination.v] widens the abstract
    order so that every γ-empty element is below everything:

    - The carrier is unchanged: no subset type, no smart constructor.
    - The order becomes [¬ is_empty a1 ∨ a1 ⊑ a2], making all
      γ-empty elements [⊑]-equivalent.
    - The join is redefined so that γ-empty elements act as identities
      ([⊥ ⊔ x = x]).
    - [ExactOrder] and [JoinIsLUB] are recovered.

    This is simpler than the [CanonicalBottom] approach (which restricts
    the carrier to a single chosen γ-empty representative and requires
    a smart constructor, a decidable equality with [bottom], and a
    subset type): here, bottom-testing is done by [non_bottomb], which
    is O(1) on the bounds. *)

Lemma non_bottombP i : reflect (non_bottom i) (non_bottomb i).
Proof.
  case: i => [[|l] [|h]] /=; try by constructor.
  apply: Z.leb_spec0.
Qed.

(** A bottom interval really does concretize to ∅. *)
Lemma non_bottom_empty i : ~ non_bottom i -> γ[itv] i ⊆⊇ ∅.
Proof.
  move=> /non_bottom_non_empty Hn.
  apply propset_equiv_empty_iff. exact: Hn.
Qed.

(** γ-emptiness of an interval, in the form [CollapsedBottom] asks. *)
Lemma itv_is_empty_iff (i : interval) :
  CollapsedBottom.is_empty itv i <-> non_bottomb i = false.
Proof.
  rewrite /CollapsedBottom.is_empty propset_equiv_empty_iff -non_bottom_non_empty.
  split=> [H | E H].
  - by case: (non_bottombP i) => // Hnb; case: (H Hnb).
  - by move: H => /non_bottombP; rewrite E.
Qed.

(** The decision procedure [CollapsedBottom] takes as a parameter. Must be
    transparent. *)
Definition itv_is_empty_dec (i : itv) :
  {CollapsedBottom.is_empty itv i} + {~ CollapsedBottom.is_empty itv i} :=
  match Sumbool.sumbool_of_bool (non_bottomb i) with
  | left E => right (fun H => Bool.diff_true_false
                                (eq_trans (eq_sym E)
                                   (proj1 (itv_is_empty_iff i) H)))
  | right E => left (proj2 (itv_is_empty_iff i) E)
  end.

(** Exact order on non-empty intervals: γ-inclusion implies abstract
    inclusion. Needed for [CollapsedBottom_ExactOrder].

    Proved via [nbitv] ([NonEmpty.ad itv non_bottom]), which has
    [ExactOrder] (via [nonempty_exact_order]). Since [i2] is also
    non-empty (witness from [i1] transfers by inclusion), both
    elements land in the [NonEmpty] carrier. *)
Lemma itv_exact_pos (i1 i2 : itv) :
  ~ CollapsedBottom.is_empty itv i1 ->
  γ[itv] i1 ⊆ γ[itv] i2 -> i1 ⊑[itv] i2.
Proof.
  move=> Hne Hsub.
  case: (non_bottombP i1) => [Hnb1 | Hnb1].
  - have Hnb2 : non_bottom i2.
    { move: Hnb1 => /non_bottom_non_empty [c Hc].
      apply non_bottom_non_empty. exists c. unfold_set in *. exact: (Hsub c Hc). }
    exact: (proj2 (exact_order (A:=nbitv) (exist _ i1 Hnb1) (exist _ i2 Hnb2)) Hsub).
  - exfalso. apply: Hne. unfold CollapsedBottom.is_empty. split.
    + rewrite /(_ ⊆ _). move=> c Hc. apply Hnb1.
      apply non_bottom_non_empty. exists c. exact: Hc.
    + move=> c [].
Qed.

(** The collapsed-bottom interval lattice. Same carrier ([interval]),
    same [γ], same meet — only [⊑] and [⊔] change. *)
Definition itv_canon_al : abstract_lattice Z :=
  CollapsedBottom.al_lub itv itv_is_empty_dec.

Definition itv_canon_ad : abstract_domain Z := al_ajsl itv_canon_al.
Definition itv_canon_ajsl : abstract_join_semilattice Z := al_ajsl itv_canon_al.

Global Instance itv_canon_join_is_lub : JoinIsLUB itv_canon_ajsl.
Proof. apply CollapsedBottom.CollapsedBottom_JoinIsLUB. apply _. Qed.

Global Instance itv_canon_exact_order : ExactOrder itv_canon_ad.
Proof. apply CollapsedBottom.CollapsedBottom_ExactOrder. exact: itv_is_empty_dec. exact: itv_exact_pos. Qed.

(** [⊔[itv_canon_ajsl]] is built from the [sumbool] [itv_is_empty_dec], whose
    [Prop] payload has no business in code.  This identifies it with the
    boolean-guarded [join_possibly_bottom] ([ZInterval.v]), so an operation may
    be written with the latter and reasoned about with the former — in
    particular inheriting [itv_canon_join_is_lub]. *)
Lemma itv_canon_join_eq (a b : interval) :
  a ⊔[itv_canon_ajsl] b = join_possibly_bottom a b.
Proof.
  rewrite /(_ ⊔[itv_canon_ajsl] _) /= /CollapsedBottom.join_lub_compat
          /itv_is_empty_dec /join_possibly_bottom.
  by case: (Sumbool.sumbool_of_bool (non_bottomb a)) => -> //;
     case: (Sumbool.sumbool_of_bool (non_bottomb b)) => ->.
Qed.

(** Being a best abstraction on [itv_canon_ad] is being a *sound* one that is
    additionally best on [itv] whenever it is non-bottom. *)
Lemma is_alpha_itv_canon_iff (a : interval) (S : ℘ Z) :
  IsAlpha (A:=itv_canon_ad) a S <->
  S ⊆ γ[itv] a /\ (non_bottomb a = true -> IsAlpha (A:=itv) a S).
Proof.
  split.
  - move=> Hc; split.
    { apply: (proj2 (Hc a)). reflexivity. }
    move=> Ea. have Hne : ~ CollapsedBottom.is_empty itv a
      by move=> /(proj1 (itv_is_empty_iff a)); rewrite Ea.
    move=> b; split.
    + move=> HS. by case: (proj1 (Hc b) HS) => [/Hne [] | Hle].
    + move=> Hle. exact: (proj2 (Hc b) (or_intror Hle)).
  - move=> [Hsub HT].
    case Ea : (non_bottomb a); last first.
    + have Hemp := proj2 (itv_is_empty_iff a) Ea.
      move=> b; split=> _; last by move=> z /Hsub /(proj1 Hemp) [].
      by left.
    + have Ha := HT Ea.
      have Hne : ~ CollapsedBottom.is_empty itv a
        by move=> /(proj1 (itv_is_empty_iff a)); rewrite Ea.
      move=> b; split.
      * move=> HS. right. exact: (proj1 (Ha b) HS).
      * case=> [Hemp | Hle]; first by case: (Hne Hemp).
        exact: (proj2 (Ha b) Hle).
Qed.

(** Non-bottom intervals are maximally reduced on [itv]. ExactOrder on
    the non-bottom subtype [nbitv] is the source — the only extra step
    is handling the case where the "competing" interval is bottom, in
    which case its [γ] is empty and the [γ]-inclusion hypothesis
    contradicts non-bottomness of [i]. *)
Lemma non_bottom_MaximallyReduced (i : interval) :
  non_bottom i -> MaximallyReduced (A:=itv) i.
Proof.
  move=> Hnb. split; first done.
  move=> i' Hsub. apply: itv_exact_pos => //.
  move=> [Hempty _]. rewrite non_bottom_non_empty in Hnb.
  move: Hnb => [c Hc]. exact: (Hempty c Hc).
Qed.

(** The [IsAlpha] reading of [non_bottom_MaximallyReduced]: a non-bottom
    interval is the best abstraction of its own concretization.  This is the
    form the α-completeness transfer function proofs want. *)
Lemma non_bottom_is_alpha_gamma (i : interval) :
  non_bottom i -> IsAlpha (A:=itv) i (γ[itv] i).
Proof.
  move=> Hnb; apply/is_alpha_iff_best_abstraction.
  exact: non_bottom_MaximallyReduced.
Qed.

(** * Building a best abstraction, one bound at a time.

    Instantiations at [Z] of the generic lemmas of [BoundAbstraction]: an
    *attained* bound is the best one, an *unbounded* set is best abstracted by
    [Top], and a *cofinal* subset shares the best abstraction of the whole
    (uniformly in [Top] and [NotTop]). *)

Lemma glbtop_of_min (l : Z) (S : ℘ Z) :
  l ∈ S -> (forall z, z ∈ S -> l <= z) ->
  IsAlpha (A:=glbtop) (WithTop.NotTop l) S.
Proof.
  exact: (BoundAbstraction.GLBUnbounded.min_is_best
            Z.le z_is_unbounded z_le_antisymm l S).
Qed.

Lemma lubtop_of_max (h : Z) (S : ℘ Z) :
  h ∈ S -> (forall z, z ∈ S -> z <= h) ->
  IsAlpha (A:=lubtop) (WithTop.NotTop h) S.
Proof.
  exact: (BoundAbstraction.LUBUnbounded.max_is_best
            Z.le z_is_unbounded_up z_le_antisymm h S).
Qed.

(** The [~~] forms are the primitive ones: their hypothesis is weaker, and it
    is what a witness extracted through a [Stable] continuation (e.g. by
    [is_alpha_glbtop_top_nn]) supplies. The plain forms are one line each. *)

Lemma glbtop_top_of_unbounded_nn (S : ℘ Z) :
  (forall M, ~ ~ (exists c, c ∈ S /\ c < M)) ->
  IsAlpha (A:=glbtop) WithTop.Top S.
Proof.
  move=> H.
  apply: (BoundAbstraction.GLBUnbounded.no_lower_bound_nn_implies_top_is_best
            Z.le z_is_unbounded z_le_antisymm S).
  move=> z Hn. apply: (H z) => -[c [Hc Hlt]].
  apply: Hn. exists c. split=> //. lia.
Qed.

Lemma lubtop_top_of_unbounded_nn (S : ℘ Z) :
  (forall M, ~ ~ (exists c, c ∈ S /\ M < c)) ->
  IsAlpha (A:=lubtop) WithTop.Top S.
Proof.
  move=> H.
  apply: (BoundAbstraction.LUBUnbounded.no_upper_bound_nn_implies_top_is_best
            Z.le z_is_unbounded_up z_le_antisymm S).
  move=> z Hn. apply: (H z) => -[c [Hc Hlt]].
  apply: Hn. exists c. split=> //. rewrite /CRelationClasses.flip. lia.
Qed.

Lemma glbtop_top_of_unbounded (S : ℘ Z) :
  (forall M, exists c, c ∈ S /\ c < M) -> IsAlpha (A:=glbtop) WithTop.Top S.
Proof.
  move=> H. apply: glbtop_top_of_unbounded_nn => M Hn. apply: Hn. exact: H.
Qed.

Lemma lubtop_top_of_unbounded (S : ℘ Z) :
  (forall M, exists c, c ∈ S /\ M < c) -> IsAlpha (A:=lubtop) WithTop.Top S.
Proof.
  move=> H. apply: lubtop_top_of_unbounded_nn => M Hn. apply: Hn. exact: H.
Qed.

Lemma glbtop_cofinal (S S' : ℘ Z) (l : glbtop) :
  S' ⊆ S -> (forall z, z ∈ S -> exists z', z' ∈ S' /\ z' <= z) ->
  IsAlpha (A:=glbtop) l S' -> IsAlpha (A:=glbtop) l S.
Proof. move=> Hsub Hcof. exact: (proj1 (BoundAbstraction.GLBUnbounded.cofinal_below_same_alpha Z.le S S' l Hsub Hcof)). Qed.

Lemma lubtop_cofinal (S S' : ℘ Z) (h : lubtop) :
  S' ⊆ S -> (forall z, z ∈ S -> exists z', z' ∈ S' /\ z <= z') ->
  IsAlpha (A:=lubtop) h S' -> IsAlpha (A:=lubtop) h S.
Proof. move=> Hsub Hcof. exact: (proj1 (BoundAbstraction.LUBUnbounded.cofinal_above_same_alpha Z.le S S' h Hsub Hcof)). Qed.

(** Both bounds at once, and in both directions. Right-to-left is the one the
    bound-at-a-time lemmas above cannot express: it carries an [IsAlpha] proved
    on a superset [S] down to a subset [S'] with the same bounds, which is how a
    transfer function assembled from α-complete pieces (whose collecting set is
    a relaxation, like a Minkowski sum, say) is shown α-complete for the set it
    is really about.

    The second and third hypotheses say that any bound of [S'] bounds [S]
    too. Combined with [S' ⊆ S] this makes [S] and [S'] share the same
    bounds. The point of stating it this way (rather than the witness form [forall z
    ∈ S, exists z' ∈ S', z' <= z] used by [glbtop_cofinal] above) is that a bound may
    be [Top]: then the obligation [S ⊆ γ Top] is trivial, while no concrete
    element could witness a bound that does not exist. *)
Lemma itv_same_alpha_same_bounds (S S' : ℘ Z) (i : interval) :
  S' ⊆ S ->
  (forall b : glbtop, S' ⊆ γ[glbtop] b -> S ⊆ γ[glbtop] b) ->
  (forall b : lubtop, S' ⊆ γ[lubtop] b -> S ⊆ γ[lubtop] b) ->
  IsAlpha (A:=itv) i S' <-> IsAlpha (A:=itv) i S.
Proof. exact: (BoundAbstraction.IntervalUnbounded.same_alpha_same_bounds Z.le S S' i). Qed.

(** The best abstraction of a set pinned between two of its own elements: both
    bounds are attained, so each is the glb (lub) of the set. *)
Lemma is_alpha_itv_attained (l h : Z) (S : ℘ Z) :
  l ∈ S -> h ∈ S -> (forall c, c ∈ S -> l <= c <= h) ->
  IsAlpha (A:=itv) (WithTop.NotTop l, WithTop.NotTop h) S.
Proof.
  move=> Hl Hh Hb; apply/Conjunction.is_alpha_pair_iff; split.
  - apply: glbtop_of_min => // z Hz. by have := Hb _ Hz; lia.
  - apply: lubtop_of_max => // z Hz. by have := Hb _ Hz; lia.
Qed.

(** When the upper bound of a non-bottom positive interval is [Top],
    any concrete set [S] best-abstracted by it must be unbounded above
    on [Z]: any candidate finite upper bound [M] would witness
    [(NotTop l, NotTop (Z.max l M))] as an overapproximation, but
    that contradicts the [IsAlpha] equivalence (since the abstract
    [Top] is not [⊑] any finite upper bound).

    Stated through a [Stable] continuation to extract the witness
    without classical reasoning, in the style of
    [Z_is_lub_attained_witness]. *)
Lemma IsAlpha_top_unbounded {G : Prop} `{Stable G} (l : Z) (S : ℘ Z) (M : Z) :
  IsAlpha (A:=itv) (WithTop.NotTop l, WithTop.Top) S ->
  ((exists c, c ∈ S /\ M < c) -> G) -> G.
Proof.
  move=> Halpha Hk.
  have HS : S ⊆ γ[itv] (WithTop.NotTop l, WithTop.Top)
    by apply: (proj2 (Halpha _)); reflexivity.
  apply: stable => Hng.
  set bad : interval := (WithTop.NotTop l, WithTop.NotTop (Z.max l M)).
  suff Habs : (WithTop.NotTop l, WithTop.Top) ⊑[itv] bad.
  { by move: Habs => /= []. }
  apply: (proj1 (Halpha bad)) => c Hc.
  have /= [Hcl _] := HS c Hc.
  unfold_set; split => /=; first exact: Hcl.
  apply: stable => Hncle.
  apply: Hng. apply: Hk.
  exists c. split; [exact Hc | lia].
Qed.

(** Lifts a sound total binary operation on intervals to nb_intervals. *)
Definition non_bottom_lift_total_binary
  (f_itv : interval -> interval -> interval)
  (f_z : Z -> Z -> Z)
  {Hsound :
    binary_overapproximation itv itv itv f_itv
      (collecting_binary_forward f_z)}
  (i1 i2 : nb_interval) : nb_interval :=
  NonEmpty.nonempty_lift_total_binary itv non_bottom non_bottom_non_empty f_itv f_z (Hsound:=Hsound) i1 i2.

(** Lifting soundness from itv to nbitv. *)
Lemma non_bottom_lift_sound
  (f_itv : interval -> interval -> interval)
  (f_z : Z -> Z -> Z)
  (Hsound : binary_overapproximation itv itv itv f_itv
              (collecting_binary_forward f_z)):
  binary_overapproximation nbitv nbitv nbitv
    (non_bottom_lift_total_binary f_itv f_z (Hsound:=Hsound))
    (collecting_binary_forward f_z).
Proof.
  move=> a2 a1 c Hc.
  rewrite gamma_nbitv_gamma_itv /=.
  apply Hsound.
  unfold_set. unfold_set in Hc.
  move: Hc => [c2 [c1 [Hc2 [Hc1 Hc0]]]].
  rewrite !gamma_nbitv_gamma_itv in Hc2, Hc1.
  by exists c2, c1.
Qed.

Lemma is_singleton_spec l h x :
  ZInterval.is_singleton (l, h) = Some x <-> (forall z, z ∈ γ[itv] (l, h) <-> z = x).
Proof.
  rewrite /ZInterval.is_singleton.
  destruct l as [|l']; destruct h as [|h'].
  - split => // Hall.
    have Hx1 : x + 1 = x by apply (proj1 (Hall (x+1))); unfold_set.
    lia.
  - split => // Hall.
    have Hxin : x ∈ γ[itv] (WithTop.Top, WithTop.NotTop h')
      by apply (proj2 (Hall x)).
    unfold_set in Hxin; simpl in Hxin.
    have Hx1 : x - 1 = x by apply (proj1 (Hall (x-1))); unfold_set; simpl; lia.
    lia.
  - split => // Hall.
    have Hxin : x ∈ γ[itv] (WithTop.NotTop l', WithTop.Top)
      by apply (proj2 (Hall x)).
    unfold_set in Hxin; simpl in Hxin.
    have Hx1 : x + 1 = x by apply (proj1 (Hall (x+1))); unfold_set; simpl; lia.
    lia.
  - case: (Z.eqb_spec l' h') => [->|Hne].
    + split.
      * case=> ->. move=> z. unfold_set; simpl. lia.
      * move=> Hall.
        have Hh : h' = x by apply (proj1 (Hall h')); unfold_set; simpl; lia.
        by rewrite Hh.
    + split => // Hall.
      have Hxin : x ∈ γ[itv] (WithTop.NotTop l', WithTop.NotTop h')
        by apply (proj2 (Hall x)).
      unfold_set in Hxin; simpl in Hxin.
      have Hl : l' = x by apply (proj1 (Hall l')); unfold_set; simpl; lia.
      have Hh : h' = x by apply (proj1 (Hall h')); unfold_set; simpl; lia.
      lia.
Qed.

(** [ZInterval.singleton k] contains [k]. *)
Lemma gamma_itv_singleton k : k ∈ γ[itv] (ZInterval.singleton k).
Proof.
  have Hspec : forall z, z ∈ γ[itv] (WithTop.NotTop k, WithTop.NotTop k) <-> z = k.
  { apply (proj1 (is_singleton_spec (WithTop.NotTop k) (WithTop.NotTop k) k)).
    simpl. by rewrite Z.eqb_refl. }
  by apply (proj2 (Hspec k)).
Qed.

Lemma is_singleton_None_two l h :
  non_bottom (l, h) -> ZInterval.is_singleton (l, h) = None ->
  exists z1 z2, z1 ∈ γ[itv] (l, h) /\ z2 ∈ γ[itv] (l, h) /\ z1 <> z2.
Proof.
  move=> /non_bottom_non_empty [c Hc] Hns.
  unfold_set in Hc.
  destruct l as [|l']; destruct h as [|h']; unfold_set in Hc; simpl in Hc.
  - exists 0, 1. unfold_set; simpl; lia.
  - exists h', (h' - 1). unfold_set; simpl; lia.
  - exists l', (l' + 1). unfold_set; simpl; lia.
  - rewrite /ZInterval.is_singleton in Hns.
    case: (Z.eqb_spec l' h') Hns => [//|Hne _].
    exists l', h'. unfold_set; simpl; lia.
Qed.

(** From [ZInterval.is_singleton (l, h) <> Some x], produce an element of γ
    distinct from [x]. Lets us reduce the four-way case split in
    [may_be_false_eqb_exact] to a uniform "find a witness avoiding y". *)
Lemma is_singleton_witness_not_x l h x :
  non_bottom (l, h) -> ZInterval.is_singleton (l, h) <> Some x ->
  exists c, c ∈ γ[itv] (l, h) /\ c <> x.
Proof.
  move=> Hnb Hns.
  case Hs: (ZInterval.is_singleton (l, h)) Hns => [y|] Hns.
  - exists y.  move/is_singleton_spec: Hs => Hs.
    split; by [apply Hs| congruence].
  - have [z1 [z2 [Hz1 [Hz2 Hne]]]] := is_singleton_None_two _ _ Hnb Hs.
    case: (Z.eq_dec z1 x) => [?|?]; [exists z2|exists z1]; split=> //.
    congruence.
Qed.

(** * Generic α-machinery for interval transfer functions.

    Attainment witnesses for glb/lub in Z, extrema of bounded sets, the
    split-at-zero decomposition of an abstracted set, and the Z-specialised
    [interval_lift2] α-completeness lemma. These are facts about the domain
    rather than about any one operation, and are shared by the [add], [mul]
    and [quot] transfer functions in Transfer_function/ZInterval/. *)

(** Attainment: from [is_glb]/[is_lub] in Z, the bound belongs to the
    set — but membership of an arbitrary [S] is not decidable, so the
    bound is delivered to a continuation under a [¬¬]-stable goal [G].
    Uses the discrete nature of Z: if [l ∉ S], then [l+1] would also be
    a lower bound, contradicting that [l] is the greatest. *)
Lemma Z_is_glb_attained_witness {G : Prop} `{Stable G} (l : Z) (S : ℘ Z) :
  GLB.is_glb Z.le l S -> ((l ∈ S) -> G) -> G.
Proof.
  move=> [Hlb Hglb] Hk. apply: stable => Hng.
  have Hnotin : ~ l ∈ S by move=> Hin; exact: Hng (Hk Hin).
  have H_lp1_lb: forall c, c ∈ S -> l+1 <= c.
  { move=> c Hc.
    have Hle := Hlb _ Hc.
    move: (Zle_lt_or_eq _ _ Hle) => [Hlt|Heq].
    - lia.
    - exfalso. apply Hnotin. rewrite Heq. exact Hc. }
  have := Hglb (l+1) H_lp1_lb. lia.
Qed.

Lemma Z_is_lub_attained_witness {G : Prop} `{Stable G} (h : Z) (S : ℘ Z) :
  LUB.is_lub Z.le h S -> ((h ∈ S) -> G) -> G.
Proof.
  move=> [Hub Hlub] Hk. apply: stable => Hng.
  have Hnotin : ~ h ∈ S by move=> Hin; exact: Hng (Hk Hin).
  have H_hm1_ub: forall c, c ∈ S -> c <= h-1.
  { move=> c Hc.
    have Hle := Hub _ Hc.
    move: (Zle_lt_or_eq _ _ Hle) => [Hlt|Heq].
    - lia.
    - exfalso. apply Hnotin. rewrite -Heq. exact Hc. }
  have := Hlub (h-1) H_hm1_ub. lia.
Qed.

(** Restricting an abstracted set to its non-positive part keeps the
    lower bound [l] as the abstraction's low bound (the low end of [S]
    is [≤ 0], hence retained). The [Top] (unbounded-below) case refutes
    every finite candidate via [is_alpha_glbtop_top_nn]. *)
Lemma glbtop_le0_restrict (l : WithTop.with_top Z) (S : ℘ Z) :
  0 ∈ γ[glbtop] l -> attained S l ->
  IsAlpha (A:=glbtop) l S ->
  IsAlpha (A:=glbtop) l {[ z | z ∈ S /\ z <= 0 ]}.
Proof.
  case: l => [|a] /= Hl0 Hatt Ha.
  - rewrite /IsAlpha => b; case: b => [|M] /=.
    + by unfold_set; split.
    + unfold_set; split; [|by []].
      move=> Hsub.
      apply: (is_alpha_glbtop_top_nn S (Z.min M 0) Ha) => -[c [Hc Hlt]].
      have Hin : c ∈ {[ z | z ∈ S /\ z <= 0 ]} by unfold_set; split=> //; lia.
      move: (Hsub c Hin); unfold_set => /=; lia.
  - move: (IsAlpha_glbtop_NotTop_is_glb Z.le a S Ha) => [Hlb Hgr].
    move: Hl0; unfold_set => Ha0.
    apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_glbtop)).
    constructor.
    + move=> z; unfold_set => -[Hz _]. exact: (Hlb z Hz).
    + move=> g Hg. apply: Hg. unfold_set; split=> //.
Qed.

(** Mirror: restricting to the non-negative part keeps the upper bound. *)
Lemma lubtop_ge0_restrict (h : WithTop.with_top Z) (S : ℘ Z) :
  0 ∈ γ[lubtop] h -> attained S h ->
  IsAlpha (A:=lubtop) h S ->
  IsAlpha (A:=lubtop) h {[ z | z ∈ S /\ 0 <= z ]}.
Proof.
  case: h => [|a] /= Hh0 Hatt Ha.
  - rewrite /IsAlpha => b; case: b => [|M] /=.
    + by unfold_set; split.
    + unfold_set; split; [|by []].
      move=> Hsub.
      apply: (is_alpha_lubtop_top_nn S (Z.max M 0) Ha) => -[c [Hc Hgt]].
      have Hin : c ∈ {[ z | z ∈ S /\ 0 <= z ]} by unfold_set; split=> //; lia.
      move: (Hsub c Hin); unfold_set => /=; lia.
  - move: (IsAlpha_lubtop_NotTop_is_lub Z.le a S Ha) => [Hub Hlo].
    move: Hh0; unfold_set => Ha0.
    apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_lubtop)).
    constructor.
    + move=> z; unfold_set => -[Hz _]. exact: (Hub z Hz).
    + move=> g Hg. apply: Hg. unfold_set; split=> //.
Qed.

(** Strict counterparts, for a *divisor*: [0] has to be excluded, so the cut is
    [z < 0] / [0 < z] rather than [z <= 0] / [0 <= z].

    The hypothesis strengthens with it.  A bound merely [<= 0] may *be* [0], and
    then the strict half is empty and the bound is no longer its glb — so
    [0 ∈ γ[glbtop] l] is not enough and [low_neg l] is what is needed.  That is
    exactly what an [across_interval] carries, which is why these apply to
    precisely the divisors that cross zero. *)
Lemma glbtop_lt0_restrict (l : WithTop.with_top Z) (S : ℘ Z) :
  low_neg l -> attained S l ->
  IsAlpha (A:=glbtop) l S ->
  IsAlpha (A:=glbtop) l {[ z | z ∈ S /\ z < 0 ]}.
Proof.
  case: l => [|a] /= Hl0 Hatt Ha.
  - rewrite /IsAlpha => b; case: b => [|M] /=.
    + by unfold_set; split.
    + unfold_set; split; [|by []].
      move=> Hsub.
      apply: (is_alpha_glbtop_top_nn S (Z.min M 0) Ha) => -[c [Hc Hlt]].
      have Hin : c ∈ {[ z | z ∈ S /\ z < 0 ]} by unfold_set; split=> //; lia.
      move: (Hsub c Hin); unfold_set => /=; lia.
  - move: (IsAlpha_glbtop_NotTop_is_glb Z.le a S Ha) => [Hlb Hgr].
    apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_glbtop)).
    constructor.
    + move=> z; unfold_set => -[Hz _]. exact: (Hlb z Hz).
    + move=> g Hg. apply: Hg. unfold_set; split=> //.
Qed.

(** Mirror: restricting to the strictly positive part keeps the upper bound. *)
Lemma lubtop_gt0_restrict (h : WithTop.with_top Z) (S : ℘ Z) :
  high_pos h -> attained S h ->
  IsAlpha (A:=lubtop) h S ->
  IsAlpha (A:=lubtop) h {[ z | z ∈ S /\ 0 < z ]}.
Proof.
  case: h => [|a] /= Hh0 Hatt Ha.
  - rewrite /IsAlpha => b; case: b => [|M] /=.
    + by unfold_set; split.
    + unfold_set; split; [|by []].
      move=> Hsub.
      apply: (is_alpha_lubtop_top_nn S (Z.max M 0) Ha) => -[c [Hc Hgt]].
      have Hin : c ∈ {[ z | z ∈ S /\ 0 < z ]} by unfold_set; split=> //; lia.
      move: (Hsub c Hin); unfold_set => /=; lia.
  - move: (IsAlpha_lubtop_NotTop_is_lub Z.le a S Ha) => [Hub Hlo].
    apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_lubtop)).
    constructor.
    + move=> z; unfold_set => -[Hz _]. exact: (Hub z Hz).
    + move=> g Hg. apply: Hg. unfold_set; split=> //.
Qed.

(** A non-empty set of integers bounded above has a greatest element.
    Classically real but not constructible, so delivered double-negated:
    if there were no maximum, every element would be strictly exceeded,
    yielding elements arbitrarily far above [c0] and contradicting the
    bound. Companion to [Z_is_lub_attained_witness] (which assumes the
    bound is already known); here we *produce* it. *)
Lemma Z_bounded_above_max_nn (B : Z) (S : ℘ Z) :
  (exists c, c ∈ S) -> (forall c, c ∈ S -> c <= B) ->
  ~ ~ (exists m, m ∈ S /\ forall z, z ∈ S -> z <= m).
Proof.
  move=> [c0 Hc0] Hbound HnM.
  have Hstep : forall z, z ∈ S -> ~ ~ (exists y, y ∈ S /\ z < y).
  { move=> z Hz Hny. apply: HnM. exists z; split=> // y Hy.
    case: (Z.le_gt_cases y z) => [//|Hgt]. exfalso; apply: Hny. by exists y. }
  have Hchain : forall n : nat, ~ ~ (exists z, z ∈ S /\ c0 + Z.of_nat n <= z).
  { elim => [|n IH].
    - move=> H. apply: H. exists c0; split; [exact Hc0 | simpl; lia].
    - move=> H. apply: IH => -[z [Hz Hzge]].
      apply: (Hstep z Hz) => -[y [Hy Hylt]].
      apply: H. exists y; split; first exact Hy. rewrite Nat2Z.inj_succ; lia. }
  apply: (Hchain (Z.to_nat (B - c0 + 1))) => -[z [Hz Hzge]].
  have Hc0b := Hbound c0 Hc0. have Hzb := Hbound z Hz.
  have HB : 0 <= B - c0 + 1 by lia.
  rewrite (Z2Nat.id _ HB) in Hzge; lia.
Qed.

(** Bound existence, exposed through a [Stable] continuation: a non-empty
    set bounded above by [B] has a lub [m ≤ B]. *)
Lemma Z_bounded_above_lub_witness {G : Prop} `{Stable G} (B : Z) (S : ℘ Z) :
  (exists c, c ∈ S) -> (forall c, c ∈ S -> c <= B) ->
  ((exists m, LUB.is_lub Z.le m S /\ m <= B /\ m ∈ S) -> G) -> G.
Proof.
  move=> Hne Hbound Hk. apply: stable => Hng.
  apply: (Z_bounded_above_max_nn B S Hne Hbound) => -[m [Hm Hmax]].
  apply: Hng; apply: Hk. exists m; split; last by split; [exact: (Hbound m Hm)|exact: Hm].
  constructor.
  - move=> z Hz. exact: (Hmax z Hz).
  - move=> z' Hz'. exact: (Hz' m Hm).
Qed.

(** Mirror: a non-empty set bounded below by [B] has a least element. *)
Lemma Z_bounded_below_min_nn (B : Z) (S : ℘ Z) :
  (exists c, c ∈ S) -> (forall c, c ∈ S -> B <= c) ->
  ~ ~ (exists m, m ∈ S /\ forall z, z ∈ S -> m <= z).
Proof.
  move=> [c0 Hc0] Hbound HnM.
  have Hstep : forall z, z ∈ S -> ~ ~ (exists y, y ∈ S /\ y < z).
  { move=> z Hz Hny. apply: HnM. exists z; split=> // y Hy.
    case: (Z.le_gt_cases z y) => [//|Hgt]. exfalso; apply: Hny. by exists y. }
  have Hchain : forall n : nat, ~ ~ (exists z, z ∈ S /\ z <= c0 - Z.of_nat n).
  { elim => [|n IH].
    - move=> H. apply: H. exists c0; split; [exact Hc0 | simpl; lia].
    - move=> H. apply: IH => -[z [Hz Hzle]].
      apply: (Hstep z Hz) => -[y [Hy Hylt]].
      apply: H. exists y; split; first exact Hy. rewrite Nat2Z.inj_succ; lia. }
  apply: (Hchain (Z.to_nat (c0 - B + 1))) => -[z [Hz Hzle]].
  have Hc0b := Hbound c0 Hc0. have Hzb := Hbound z Hz.
  have HB : 0 <= c0 - B + 1 by lia.
  rewrite (Z2Nat.id _ HB) in Hzle; lia.
Qed.

Lemma Z_bounded_below_glb_witness {G : Prop} `{Stable G} (B : Z) (S : ℘ Z) :
  (exists c, c ∈ S) -> (forall c, c ∈ S -> B <= c) ->
  ((exists m, GLB.is_glb Z.le m S /\ B <= m /\ m ∈ S) -> G) -> G.
Proof.
  move=> Hne Hbound Hk. apply: stable => Hng.
  apply: (Z_bounded_below_min_nn B S Hne Hbound) => -[m [Hm Hmin]].
  apply: Hng; apply: Hk. exists m; split; last by split; [exact: (Hbound m Hm)|exact: Hm].
  constructor.
  - move=> z Hz. exact: (Hmin z Hz).
  - move=> z' Hz'. exact: (Hz' m Hm).
Qed.

(** Z.add is monotone, order-reflecting, and reaches ±∞ in both arguments. *)
Lemma Zadd_monotone_binop : monotone_binop Z.le Z.le Z.le Z.add.
Proof. move=> a1 a1' a2 a2' Ha1 Ha2. lia. Qed.

Lemma Zadd_order_reflecting_left : order_reflecting_left Z.le Z.le Z.add.
Proof. move=> a1 a2 b H. lia. Qed.

Lemma Zadd_order_reflecting_right : order_reflecting_right Z.le Z.le Z.add.
Proof. move=> a b1 b2 H. lia. Qed.

(** Register Z as a [GlbsAreMins] / [LubsAreMaxs] domain.

    The proof bodies above ([Z_is_glb_attained_witness],
    [Z_is_lub_attained_witness]) rely on Z's discreteness ([l+1] is
    still a lower bound if [l ∉ S]). They satisfy the abstract
    [GlbsAreMins] / [LubsAreMaxs] interface in [BoundAbstraction.v],
    which makes the generic [itv_attained_low/high_witness] available
    on Z by typeclass resolution. *)
Global Instance Z_glbs_are_mins : GlbsAreMins Z.le.
Proof. by move=> G HSt l S; exact: Z_is_glb_attained_witness. Qed.

Global Instance Z_lubs_are_maxs : LubsAreMaxs Z.le.
Proof. by move=> G HSt h S; exact: Z_is_lub_attained_witness. Qed.

(** Read at [t ∈ γ l]: if the abstracted set's lower bound does not exclude
    [t], then the set really does have an element at or below [t] — attained
    when the bound is finite, and somewhere below when it is [Top]. We deliver
    this element when the goal is [Stable]. *)
Lemma glbtop_below_witness {G : Prop} `{Stable G}
  (l : WithTop.with_top Z) (S : ℘ Z) (t : Z) :
  t ∈ γ[glbtop] l -> IsAlpha (A:=glbtop) l S ->
  ((exists c, c ∈ S /\ c <= t) -> G) -> G.
Proof.
  case: l => [|a] /= Ht Ha Hk.
  - apply: (is_alpha_glbtop_top_witness S (t + 1) Ha) => -[c [Hc Hlt]].
    apply: Hk. exists c; split=> //; lia.
  - move: (IsAlpha_glbtop_NotTop_is_glb Z.le a S Ha) => Hglb.
    apply: (Z_is_glb_attained_witness a S Hglb) => Hain.
    apply: Hk. by exists a.
Qed.

Lemma lubtop_above_witness {G : Prop} `{Stable G}
  (h : WithTop.with_top Z) (S : ℘ Z) (t : Z) :
  t ∈ γ[lubtop] h -> IsAlpha (A:=lubtop) h S ->
  ((exists c, c ∈ S /\ t <= c) -> G) -> G.
Proof.
  case: h => [|a] /= Ht Ha Hk.
  - apply: (is_alpha_lubtop_top_witness S (t - 1) Ha) => -[c [Hc Hgt]].
    apply: Hk. exists c; split=> //; lia.
  - move: (IsAlpha_lubtop_NotTop_is_lub Z.le a S Ha) => Hlub.
    apply: (Z_is_lub_attained_witness a S Hlub) => Hain.
    apply: Hk. by exists a.
Qed.

(** Split the abstraction of an across-zero abstract set into its two
    sign halves: the non-positive part keeps the low bound [l2] and gets
    a fresh finite high bound [m ≤ 0] (its lub); the non-negative part
    keeps the high bound [h2] and a fresh low bound [p ≥ 0] (its glb).
    Delivered through a [Stable] continuation (the fresh bounds come from
    the bound-existence witnesses, the inherited ones from the
    restriction lemmas). *)
Lemma itv_split_at_zero_alpha {G : Prop} `{Stable G}
  (l2 h2 : WithTop.with_top Z) (S2 : ℘ Z) :
  0 ∈ γ[glbtop] l2 -> 0 ∈ γ[lubtop] h2 -> (exists c, c ∈ S2) ->
  IsAlpha (A:=itv) (l2, h2) S2 ->
  (forall m p,
     m <= 0 -> 0 <= p ->
     IsAlpha (A:=itv) (l2, WithTop.NotTop m) {[ z | z ∈ S2 /\ z <= 0 ]} ->
     IsAlpha (A:=itv) (WithTop.NotTop p, h2) {[ z | z ∈ S2 /\ 0 <= z ]} ->
     m ∈ S2 -> p ∈ S2 -> G)
  -> G.
Proof.
  move=> Hl0 Hh0 Hex Ha Hk.
  move: (Ha) => /Conjunction.is_alpha_pair_iff [Hglb Hlub].
  apply: (itv_attained_low_witness l2 h2 S2 Ha Hex) => Hatl.
  apply: (itv_attained_high_witness l2 h2 S2 Ha Hex) => Hath.
  have Hglb' := glbtop_le0_restrict l2 S2 Hl0 Hatl Hglb.
  have Hlub' := lubtop_ge0_restrict h2 S2 Hh0 Hath Hlub.
  apply: (glbtop_below_witness l2 S2 0 Hl0 Hglb) => Hne_neg.  
  apply: (lubtop_above_witness h2 S2 0 Hh0 Hlub) => Hne_pos.
  have Hb_neg : forall c, c ∈ {[ z | z ∈ S2 /\ z <= 0 ]} -> c <= 0
    by move=> c Hc; unfold_set in Hc; tauto.
  have Hb_pos : forall c, c ∈ {[ z | z ∈ S2 /\ 0 <= z ]} -> 0 <= c
    by move=> c Hc; unfold_set in Hc; tauto.
  have Hne_neg' : exists c, c ∈ {[ z | z ∈ S2 /\ z <= 0 ]}
    by move: Hne_neg => [c [Hc Hc0]]; exists c; unfold_set; split.
  have Hne_pos' : exists c, c ∈ {[ z | z ∈ S2 /\ 0 <= z ]}
    by move: Hne_pos => [c [Hc Hc0]]; exists c; unfold_set; split.
  apply: (Z_bounded_above_lub_witness 0 _ Hne_neg' Hb_neg) => -[m [Hlubm [Hm0 Hmemm]]].
  apply: (Z_bounded_below_glb_witness 0 _ Hne_pos' Hb_pos) => -[p [Hglbp [Hp0 Hmemp]]].
  unfold_set in Hmemm; unfold_set in Hmemp.
  apply: (Hk m p ltac:(lia) ltac:(lia) _ _ (proj1 Hmemm) (proj1 Hmemp)).
  - apply/Conjunction.is_alpha_pair_iff; split; first exact Hglb'.
    apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_lubtop)). exact Hlubm.
  - apply/Conjunction.is_alpha_pair_iff; split; last exact Hlub'.
    apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_glbtop)). exact Hglbp.
Qed.

(** Strict counterparts of [across_le0_witness] / [across_ge0_witness]: an
    element strictly on one side of 0.  [low_neg] / [high_pos] replace the
    [0 ∈ γ[..]] hypotheses, and in exchange the non-emptiness witness is no
    longer needed — a bound that is [Top] already says the set is unbounded, and
    a finite one is attained. *)
Lemma across_lt0_witness {G : Prop} `{Stable G}
  (l : WithTop.with_top Z) (S : ℘ Z) :
  low_neg l -> IsAlpha (A:=glbtop) l S ->
  ((exists c, c ∈ S /\ c < 0) -> G) -> G.
Proof.
  case: l => [|a] /= Hl0 Ha Hk.
  - apply: (is_alpha_glbtop_top_witness S 0 Ha) => -[c [Hc Hlt]].
    apply: Hk. by exists c.
  - move: (IsAlpha_glbtop_NotTop_is_glb Z.le a S Ha) => Hglb.
    apply: (Z_is_glb_attained_witness a S Hglb) => Hain.
    apply: Hk. by exists a.
Qed.

Lemma across_gt0_witness {G : Prop} `{Stable G}
  (h : WithTop.with_top Z) (S : ℘ Z) :
  high_pos h -> IsAlpha (A:=lubtop) h S ->
  ((exists c, c ∈ S /\ 0 < c) -> G) -> G.
Proof.
  case: h => [|a] /= Hh0 Ha Hk.
  - apply: (is_alpha_lubtop_top_witness S 0 Ha) => -[c [Hc Hgt]].
    apply: Hk. by exists c.
  - move: (IsAlpha_lubtop_NotTop_is_lub Z.le a S Ha) => Hlub.
    apply: (Z_is_lub_attained_witness a S Hlub) => Hain.
    apply: Hk. by exists a.
Qed.

(** Split the abstraction of a set that does not contain 0 into its two strict
    sign halves:

    - the strictly negative part keeps the low bound [l] and gets a fresh finite
      high bound [m ≤ -1] (its lub);

    - the strictly positive part keeps the high bound [h] and gets a fresh low
      bound [p ≥ 1] (its glb).

    This is useful for all operations that require splitting at 0 excluding 0
    (division, remainder), and is an opportunity for domains like congruence and
    known-bits to improve the estimate for the value of [p] and [m]. The bounds
    [m] and [p] are extracted from [S] (they are the largest negative and
    smallest positive elements of [S]) but the extraction is classical, so the
    lemma is in CPS: the continuation receives [m] and [p] together with their
    [IsAlpha] facts on the two halves.

    The [low_neg l] / [high_pos h] guarantee the halves are non-empty, and they
    are exactly what [across_interval] carries. *)
Lemma itv_split_at_zero_strict_alpha {G : Prop} `{Stable G}
  (l h : WithTop.with_top Z) (S : ℘ Z) :
  low_neg l -> high_pos h -> (exists c, c ∈ S) ->
  IsAlpha (A:=itv) (l, h) S ->
  (forall m p,
     m ∈ S -> m < 0 -> p ∈ S -> 0 < p ->
     IsAlpha (A:=itv) (l, WithTop.NotTop m) {[ z | z ∈ S /\ z < 0 ]} ->
     IsAlpha (A:=itv) (WithTop.NotTop p, h) {[ z | z ∈ S /\ 0 < z ]} -> G)
  -> G.
Proof.
  move=> Hl Hh Hex Ha Hk.
  move: (Ha) => /Conjunction.is_alpha_pair_iff [Hglb Hlub].
  apply: (itv_attained_low_witness l h S Ha Hex) => Hatl.
  apply: (itv_attained_high_witness l h S Ha Hex) => Hath.
  have Hglb' := glbtop_lt0_restrict l S Hl Hatl Hglb.
  have Hlub' := lubtop_gt0_restrict h S Hh Hath Hlub.
  apply: (across_lt0_witness l S Hl Hglb) => Hne_neg.
  apply: (across_gt0_witness h S Hh Hlub) => Hne_pos.
  have Hb_neg : forall c, c ∈ {[ z | z ∈ S /\ z < 0 ]} -> c <= -1
    by move=> c Hc; unfold_set in Hc; lia.
  have Hb_pos : forall c, c ∈ {[ z | z ∈ S /\ 0 < z ]} -> 1 <= c
    by move=> c Hc; unfold_set in Hc; lia.
  have Hne_neg' : exists c, c ∈ {[ z | z ∈ S /\ z < 0 ]}
    by move: Hne_neg => [c [Hc Hc0]]; exists c; unfold_set; split.
  have Hne_pos' : exists c, c ∈ {[ z | z ∈ S /\ 0 < z ]}
    by move: Hne_pos => [c [Hc Hc0]]; exists c; unfold_set; split.
  apply: (Z_bounded_above_lub_witness (-1) _ Hne_neg' Hb_neg) => -[m [Hlubm [Hm0 Hmemm]]].
  apply: (Z_bounded_below_glb_witness 1 _ Hne_pos' Hb_pos) => -[p [Hglbp [Hp0 Hmemp]]].
  unfold_set in Hmemm; unfold_set in Hmemp.
  apply: (Hk m p (proj1 Hmemm) ltac:(lia) (proj1 Hmemp) ltac:(lia)).
  - apply/Conjunction.is_alpha_pair_iff; split; first exact Hglb'.
    apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_lubtop)). exact Hlubm.
  - apply/Conjunction.is_alpha_pair_iff; split; last exact Hlub'.
    apply (weak_α_relation_spec (WeakAlphaRelation:=is_alpha_glbtop)). exact Hglbp.
Qed.

(** Z-specialised variant of [interval_lift2_monotone_alpha_complete]:
    attainment is discharged internally via Z's discreteness
    ([itv_attained_*_witness] route through [Z_is_glb/lub_attained_witness]),
    so callers only supply monotonicity, order-reflection, the four
    [reach] facts, and non-emptiness of the operand sets.

    This is the recommended entry point for proving best abstraction of
    a Z-valued binary operator on [itv]. *)
Lemma Z_interval_lift2_alpha_complete
      (f : Z -> Z -> Z)
      (Hmono : monotone_binop Z.le Z.le Z.le f)
      (Hrefl : order_reflecting_left Z.le Z.le f)
      (Hrefr : order_reflecting_right Z.le Z.le f)
      (Hrbl : reach_below_left Z.le f) (Hrbr : reach_below_right Z.le f)
      (Hral : reach_above_left Z.le f) (Hrar : reach_above_right Z.le f)
      (i2 i1 : interval) (S2 S1 : ℘ Z) :
  (exists c, c ∈ S2) -> (exists c, c ∈ S1) ->
  binary_alpha_complete itv itv itv (interval_lift2 f)
    (collecting_binary_forward f) i2 i1 S2 S1.
Proof.
  rewrite /binary_alpha_complete => Hex2 Hex1 Ha2 Ha1.
  case: i2 Ha2 => l2 h2 Ha2; case: i1 Ha1 => l1 h1 Ha1.
  apply: (itv_attained_low_witness  l2 h2 S2 Ha2 Hex2) => Hatl2.
  apply: (itv_attained_high_witness l2 h2 S2 Ha2 Hex2) => Hath2.
  apply: (itv_attained_low_witness  l1 h1 S1 Ha1 Hex1) => Hatl1.
  apply: (itv_attained_high_witness l1 h1 S1 Ha1 Hex1) => Hath1.
  apply: (interval_lift2_monotone_alpha_complete
           Z.le Z.le Z.le z_is_unbounded z_is_unbounded_up z_le_antisymm
           f _ _ _ l2 h2 l1 h1 S2 S1); assumption.
Qed.



(** * The sign-definite intervals smart constructors. *)

(** Building a sign-definite interval from its bounds.  A lemma that fixes the
    bounds and their sign states its operand this way. *)
Definition pos_itv (l : Z) (h : WithTop.with_top Z)
  (Hl : 0 < l) (Hnb : non_bottom (WithTop.NotTop l, h)) : pos_interval :=
  exist _ (WithTop.NotTop l, h) (conj Hnb Hl).

Definition neg_itv (l : WithTop.with_top Z) (h : Z)
  (Hh : h < 0) (Hnb : non_bottom (l, WithTop.NotTop h)) : neg_interval :=
  exist _ (l, WithTop.NotTop h) (conj Hnb Hh).

(** An [across_interval] is non-bottom: its low bound is at most -1 and its
    high bound at least 1. *)
Lemma across_non_bottom (i : interval) :
  low_neg (fst i) -> high_pos (snd i) -> non_bottom i.
Proof. case: i => [[|l'] [|h']] //= Hl Hh; lia. Qed.

(** The two halves an [across_interval] splits into at ∓1 are themselves
    non-bottom, hence best abstractions of their own γ. *)
Lemma across_neg_half_non_bottom (l : WithTop.with_top Z) :
  low_neg l -> non_bottom (l, WithTop.NotTop (-1)).
Proof. case: l => [|z] /= Hz //; unfold_set; simpl; lia. Qed.

Lemma across_pos_half_non_bottom (h : WithTop.with_top Z) :
  high_pos h -> non_bottom (WithTop.NotTop 1, h).
Proof. case: h => [|z] /= Hz //; unfold_set; simpl; lia. Qed.

(** The interval's own [divisor_snap]: [classify_divisor] with the crossing
    case resolved at ∓1, which is the best a plain interval can do — it knows
    the divisor straddles zero but not which non-zero values are actually
    there.  A domain that does know supplies a sharper [divisor_snap] and
    inherits the whole quotient chain unchanged; that is the point of the
    indirection. *)
Definition across_neg_itv (i : across_interval) : neg_interval :=
  neg_itv (fst (`i)) (-1) ltac:(lia)
    (across_neg_half_non_bottom _ (proj1 (proj2_sig i))).

Definition across_pos_itv (i : across_interval) : pos_interval :=
  pos_itv 1 (snd (`i)) ltac:(lia)
    (across_pos_half_non_bottom _ (proj2 (proj2_sig i))).

(** The ∓1 halves hull back to the interval they came from — which is why
    [snapped_interval] agrees with the operand in the crossing case, and so why
    the uniform "hull of the halves" reading costs nothing here. *)
Lemma across_hull (l h : WithTop.with_top Z) :
  low_neg l -> high_pos h ->
  ZInterval.join (l, WithTop.NotTop (-1)) (WithTop.NotTop 1, h) = (l, h).
Proof. by case: l => [|l']; case: h => [|h'] /= Hl Hh; f_equal; f_equal; lia. Qed.

Definition itv_divisor_snap (i : nb_interval) : divisor_snap :=
  match classify_divisor i with
  | DivPos p => SnapPos p
  | DivNeg n => SnapNeg n
  | DivZero => SnapZero
  | DivAcross Hl Hh =>
      let a : across_interval := exist _ (`i) (conj Hl Hh) in
      SnapAcross (across_neg_itv a) (across_pos_itv a)
  end.

(** [snapped_interval] of the interval's own snap is the sanitized payload in
    the sign-definite cases and the operand itself in the crossing one — the
    ∓1 halves hull back to it ([across_hull]).  Stating it this way keeps
    [snapped_interval] index-free while letting the proofs below case on
    [classify_divisor] as they did before. *)
Lemma itv_snapped_interval (i : nb_interval) :
  snapped_interval (itv_divisor_snap i) =
  match classify_divisor i with
  | DivPos p => `p
  | DivNeg n => `n
  | DivZero => ZInterval.bottom
  | DivAcross _ _ => `i
  end.
Proof.
  rewrite /itv_divisor_snap.
  case: (classify_divisor i) => [iP | iN | | Hl Hh] //=.
  move: Hl Hh; case: (`i) => [l h] /= Hl Hh.
  exact: across_hull.
Qed.

Lemma classify_Pos_inv l h : classify (l, h) = Pos ->
  exists l', l = WithTop.NotTop l' /\ 0 <= l'.
Proof.
  rewrite /classify; case: l => [|x]; case: h => [|y] //.
  - by case: (y <=? 0)%Z.
  - case E: (x >=? 0)%Z => // _.
    by exists x; split=> //; apply Z.geb_le in E; lia.
  - case E: (x >=? 0)%Z; [| by case: (y <=? 0)%Z] => _.
    by exists x; split=> //; apply Z.geb_le in E; lia.
Qed.

Lemma classify_Neg_inv l h : classify (l, h) = Neg ->
  exists h', h = WithTop.NotTop h' /\ h' <= 0.
Proof.
  rewrite /classify; case: l => [|x]; case: h => [|y] //.
  - case E: (y <=? 0)%Z => // _; exists y; split=> //. by apply Z.leb_le.
  - by case: (x >=? 0)%Z.
  - case: (x >=? 0)%Z => //.
    case E: (y <=? 0)%Z => // _; exists y; split=> //; by apply Z.leb_le.
Qed.

Local Lemma geb0_false x : (x >=? 0)%Z = false -> x < 0.
Proof. rewrite Z.geb_leb. move/Z.leb_gt. lia. Qed.

Lemma classify_Across_inv l h :
  non_bottom (l, h) -> classify (l, h) = Across ->
  0 ∈ γ[glbtop] l /\ 0 ∈ γ[lubtop] h.
Proof.
  rewrite /classify; case: l => [|x]; case: h => [|y] => Hnb //.
  - case E: (y <=? 0)%Z => // _.
    split; [by unfold_set | unfold_set => /=; move/Z.leb_gt: E; lia].
  - case E: (x >=? 0)%Z => // _.
    split; [unfold_set => /=; move/geb0_false: E; lia | by unfold_set].
  - case E1: (x >=? 0)%Z => //.
    case E2: (y <=? 0)%Z => // _.
    split; [unfold_set => /=; move/geb0_false: E1; lia
           | unfold_set => /=; move/Z.leb_gt: E2; lia].
Qed.

