(* Z_interval.v - Interval arithmetic for integers *)
(* Noth: there are intervals in mathcomp; we could reuse their notations. *)

(* STATUS (per transfer function; ladder: sound < best < exact < α-complete):
     add:  sound + best (α-complete)  -- interval_add_alpha_complete, nb_interval_add_exact
     opp:  exact                      -- interval_opp_exact
     sub:  sound + exact (non-bottom) -- nb_interval_sub_exact
     quot: best, all 9 sign cases     -- interval_quot_*_best, interval_quot_full_best
     mul:  sound + best (α-complete)  -- interval_mul_opt_best, interval_mul_opt_alpha_complete
     leb:  exact                      -- nbinterval_leb_exact

   Transfer functions already split out into Transfer_function/ZInterval/:
     eqb:  exact                      -- EqbTheory.v

   NOTE: this file still bundles the computational core (the extractable
   [interval_*] definitions) and its mathematical theory (soundness / best /
   α-completeness proofs). The Comp/Theory split prescribed by architecture.org
   is deferred. *)

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
Definition interval := prod (WithTop.with_top Z) (WithTop.with_top Z).
Definition itv : abstract_lattice Z := IntervalUnbounded.al Z_CL.

(** Intervals are convex: [γ[itv] (l,h)] contains every point lying between
    two of its members. Specialisation of [IntervalUnbounded.convex]. *)
Lemma itv_convex (l h : WithTop.with_top Z) (a b x : Z) :
  a ∈ γ[itv] (l, h) -> b ∈ γ[itv] (l, h) -> a <= x -> x <= b ->
  x ∈ γ[itv] (l, h).
Proof. exact: IntervalUnbounded.convex. Qed.

Definition non_bottom := IntervalUnbounded.non_bottom Z_CL.

Definition nb_interval: Type := { i: interval | non_bottom i }.

(** A specific γ-empty interval, [(NotTop 1, NotTop 0)], representing
    the empty set of integers. Used as a result in division-by-zero. *)
Definition bottom := (WithTop.NotTop 1, WithTop.NotTop 0).

Definition nbitv : abstract_domain Z := NonEmpty.ad itv non_bottom.

Lemma gamma_nbitv_gamma_itv c i: c ∈ γ[nbitv] i <-> c ∈ γ[itv] (`i).
Proof.
  move: i => [[[|l] [|h]] P] //=.
Qed.



Definition glb_gammab (l:glb) z := Z.leb l z.
Instance glb_gammaP: forall l z, AutoReflect(z ∈ γ[glb] l)(glb_gammab l z).
Proof. apply/Z.leb_spec0. Qed.

Definition lub_gammab (l:lub) z := Z.leb z l.
Instance lub_gammaP: forall l z, AutoReflect(z ∈ γ[lub] l)(lub_gammab l z).
Proof. move => l z. apply/Z.leb_spec0. Qed.


Definition itv_gammab (i:interval) z :=
  (let (a, b) := i in
   match a with
   | WithTop.Top => true
   | WithTop.NotTop a0 => lub_gammab z a0
   end &&
     match b with
     | WithTop.Top => true
     | WithTop.NotTop a0 => glb_gammab z a0
     end).

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
  
(** Exact order. *)

Global Instance z_leP (z2 z1:Z): (AutoReflect(z2 <= z1)(Z.leb z2 z1)).
Proof. apply Z.leb_spec0. Qed.

Definition glbtop_is_includedb a2 a1 := 
  match a1 with
      | WithTop.Top => true
      | WithTop.NotTop a1 =>
          match a2 with
          | WithTop.Top => false
          | WithTop.NotTop a2 => Z.leb a1 a2
          end
  end.
Global Instance glbtop_is_includedP a2 a1 :
  AutoReflect(a2 ⊑[glbtop] a1)(glbtop_is_includedb a2 a1).
Proof.
  { apply WithTop.is_includedP. apply _. }
Qed.

Definition lubtop_is_includedb a2 a1 := 
  match a1 with
      | WithTop.Top => true
      | WithTop.NotTop a1 =>
          match a2 with
          | WithTop.Top => false
          | WithTop.NotTop a2 => Z.leb a2 a1
          end
  end.
Global Instance lubtop_is_includedP a2 a1 :
  AutoReflect(a2 ⊑[lubtop] a1)(lubtop_is_includedb a2 a1).
Proof.
{ apply WithTop.is_includedP. apply _. }
Qed.

Definition itv_is_includedb (a2 a1: interval) := 
  let (l2,h2) := a2 in let (l1,h1) := a1 in glbtop_is_includedb l2 l1 && lubtop_is_includedb h2 h1.
Global Instance is_includedP a2 a1:
  (AutoReflect(a2 ⊑[itv] a1)(itv_is_includedb a2 a1)).
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

(** Interval join and meet are the Conjunction join/meet of the
    GLBUnbounded and LUBUnbounded lattices. *)
Definition join_itv : interval -> interval -> interval :=
  Conjunction.join (GLBUnbounded.al Z_CL) (LUBUnbounded.al Z_CL).

Definition min_opt : WithTop.with_top Z -> WithTop.with_top Z -> WithTop.with_top Z :=
  (⊔[GLBUnbounded.al Z_CL]).

Definition max_opt : WithTop.with_top Z -> WithTop.with_top Z -> WithTop.with_top Z :=
  (⊔[LUBUnbounded.al Z_CL]).

Global Instance itv_join_is_lub : JoinIsLUB itv :=
  IntervalUnbounded.IntervalUnbounded_JoinIsLUB Z_CL.

(** Non-bottom intervals: non_bottom is equivalent to non-empty concretization. *)
Lemma non_bottom_non_empty:
  forall i:interval, (non_bottom i) <->  exists c, c ∈ γ[itv] i.
Proof. exact (IntervalUnbounded.non_bottom_non_empty Z_CL 0). Qed.

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

(** Boolean form of [non_bottom], for decidability of γ-emptiness. *)
Definition non_bottomb (i : interval) : bool :=
  match i with
  | (WithTop.Top, _) => true
  | (_, WithTop.Top) => true
  | (WithTop.NotTop l, WithTop.NotTop h) => Z.leb l h
  end.

Lemma non_bottombP i : reflect (non_bottom i) (non_bottomb i).
Proof.
  case: i => [[|l] [|h]] /=; try by constructor.
  apply: Z.leb_spec0.
Qed.

(** Decidability of γ-emptiness for intervals. *)
Definition itv_is_empty_dec (i : itv) :
  {CollapsedBottom.is_empty itv i} + {~ CollapsedBottom.is_empty itv i}.
Proof.
  unfold CollapsedBottom.is_empty.
  case: (non_bottombP i) => [Hnb | Hnb].
  - right. unfold_set. move=> Hsub.
    rewrite non_bottom_non_empty in Hnb.
    move: Hnb => [c Hc].
    exact: (proj1 Hsub c Hc).
  - left. rewrite non_bottom_non_empty in Hnb.
    split => //.
    rewrite /(_ ⊆ _).
    move => c H. exfalso. 
    apply: Hnb. by exists c.
Qed.

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

(** ** Singleton detection.

    [is_singleton l h = Some x] exactly when the interval [[l,h]]
    concretizes to the single value [x]. Generic over interval bounds,
    so it serves any "constant operand" transfer-function case; the
    [prod_ajsl] wrapper in [ZIntervalCongruence] delegates to it. *)
Definition is_singleton (l h : WithTop.with_top Z) : option Z :=
  match l, h with
  | WithTop.NotTop l', WithTop.NotTop h' =>
      if Z.eqb l' h' then Some l' else None
  | _, _ => None
  end.

Lemma is_singleton_spec l h x :
  is_singleton l h = Some x <-> (forall z, z ∈ γ[itv] (l, h) <-> z = x).
Proof.
  rewrite /is_singleton.
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

Lemma is_singleton_None_two l h :
  non_bottom (l, h) -> is_singleton l h = None ->
  exists z1 z2, z1 ∈ γ[itv] (l, h) /\ z2 ∈ γ[itv] (l, h) /\ z1 <> z2.
Proof.
  move=> /non_bottom_non_empty [c Hc] Hns.
  unfold_set in Hc.
  destruct l as [|l']; destruct h as [|h']; unfold_set in Hc; simpl in Hc.
  - exists 0, 1. unfold_set; simpl; lia.
  - exists h', (h' - 1). unfold_set; simpl; lia.
  - exists l', (l' + 1). unfold_set; simpl; lia.
  - rewrite /is_singleton in Hns.
    case: (Z.eqb_spec l' h') Hns => [//|Hne _].
    exists l', h'. unfold_set; simpl; lia.
Qed.

(** From [is_singleton l h <> Some x], produce an element of γ
    distinct from [x]. Lets us reduce the four-way case split in
    [may_be_false_eqb_exact] to a uniform "find a witness avoiding y". *)
Lemma is_singleton_witness_not_x l h x :
  non_bottom (l, h) -> is_singleton l h <> Some x ->
  exists c, c ∈ γ[itv] (l, h) /\ c <> x.
Proof.
  move=> Hnb Hns.
  case Hs: (is_singleton l h) Hns => [y|] Hns.
  - exists y.  move/is_singleton_spec: Hs => Hs.
    split; by [apply Hs| congruence].
  - have [z1 [z2 [Hz1 [Hz2 Hne]]]] := is_singleton_None_two _ _ Hnb Hs.
    case: (Z.eq_dec z1 x) => [?|?]; [exists z2|exists z1]; split=> //.
    congruence.
Qed.

(** * Transfer functions. *)

Section Interval_add.

Definition interval_add (i2 i1: interval) : interval :=
  let (l2,h2) := i2 in
  let (l1,h1) := i1 in
  (WithTop.lift2 Z.add l2 l1, WithTop.lift2 Z.add h2 h1).

Lemma interval_add_sound:
  binary_overapproximation itv itv itv interval_add
    (collecting_binary_forward Z.add).
Proof.
  overapproximation_proof.
  move: a2 a1 Hc2_in_a2 Hc1_in_a1 => [[|l2] [|h2]] [[|l1] [|h1]] Hc2_in_a2 Hc1_in_a1;
  unfold_set; unfold_set in Hc2_in_a2; unfold_set in Hc1_in_a1; simpl in *; try lia.
Qed.

Example interval_add_not_exact:
  ~ (binary_exact itv itv itv interval_add (collecting_binary_forward Z.add)).
Proof.
  (* 4 belongs to [1,0] + [3,8], even if gamma([1,0]) is empty. *)
  set a2 := (WithTop.NotTop 1, WithTop.NotTop 0).
  set a1 := (WithTop.NotTop 3, WithTop.NotTop 8).  
  set c0 := 4.
  (* TODO: simplify; this should be dischargeable by computation. It needs a
     [forall]-style iterator over γ, so that finite sets can be computed and
     compared directly. *)
  assert(Hc0_in_intervaladd: c0 ∈ γ[itv] (interval_add a2 a1))
    by solve_with_autoreflect.
  move /(_ a2 a1). to_set.
  have HU := unfold_set_equiv. unfold_set.
  move /(_ c0). unfold γ.
  move=> H. apply H in Hc0_in_intervaladd.
  (* move: Hc0_in_intervaladd. *)
  unfold_set in Hc0_in_intervaladd. simpl in Hc0_in_intervaladd.
  move: Hc0_in_intervaladd => [c2 [c1 [Hc2_in_a2 [Hc1_in_a1 defc0]]]]; lia.
Qed.  

Definition nb_interval_add := non_bottom_lift_total_binary interval_add Z.add (Hsound:=interval_add_sound).

(** Completeness of non-bottom intervals. *)
Lemma nb_interval_add_gamma_complete:
  binary_underapproximation nbitv nbitv nbitv nb_interval_add
    (collecting_binary_forward Z.add).
Proof.
  move=> [i2 P2] [i1 P1] c0 Hc0.
  rewrite gamma_nbitv_gamma_itv /= in Hc0.
  have HU := unfold_set_equiv.
  move: i2 i1 P2 P1 Hc0 => [[|l2] [|h2]] [[|l1] [|h1]] P2 P1 Hc0;
  simpl in *; unfold_set in Hc0; unfold_set.
  Ltac finish := repeat split; lia.
  (* When the arguments are very unconstrained, a single witness
     suffices.  We fix c2/c1 to this bound and chose the other
     accordingly. When the interval is top, we arbitrarily chose 0 as
     the witness. *)
  all: try (exists c0, 0; finish).
  all: try (exists (c0 - h1), h1; finish).
  all: try (exists (c0 - l1), l1; finish).
  all: try (exists h2, (c0 - h2); finish).
  all: try (exists l2, (c0 - l2); finish).

  (* [l2,h2]+l1 and [l2,h2]+h1 always cover [l2+l1, h2+h1]: for any c0
     in the sum, either c0 ≤ l2+h1 (pick c2=l2, c1=c0-l2) or c0 ≥
     l2+h1 (pick c1=h1, c2=c0-h1). Both cases satisfy the bounds
     because l2 ≤ h2 and l1 ≤ h1.

     Similarly, either c0 <= l1 + h2, or c0 >= l1 + h2. Depending on
     where is the bound, we must choose one decomposition or the
     other (and both work when both intervals are finite). *)
  all: try (destruct (Z.le_ge_cases l1 (c0 - h2));
            [exists h2, (c0 - h2) | exists (c0 - l1), l1]; finish).
  all: destruct (Z.le_ge_cases (c0 - l2) h1);
    [exists l2, (c0 - l2) | exists (c0 - h1), h1]; finish.
Qed.

Lemma nb_interval_add_exact:
  binary_exact nbitv nbitv nbitv nb_interval_add
    (collecting_binary_forward Z.add).
Proof.
  move=> a2 a1; split.
  - apply nb_interval_add_gamma_complete.
  - apply non_bottom_lift_sound.
Qed.

(** ** Best abstraction for [interval_add] applied to abstract sets.

    Given [IsAlpha (l_i, h_i) S_i] for both operands, the resulting
    interval [interval_add (l_1,h_1) (l_2,h_2)] is the most precise
    abstraction of the Minkowski sum [{a + b | a ∈ S_1, b ∈ S_2}].

    The proof leverages the fact that [Z.add] admits an inverse
    (subtraction), so optimality follows without needing the glb/lub
    to be attained in [S_i]. Inhabitance of both sets is needed to
    constrain the result when bounds are infinite or to use the
    subtraction trick when bounds are finite. *)

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
  ((exists m, LUB.is_lub Z.le m S /\ m <= B) -> G) -> G.
Proof.
  move=> Hne Hbound Hk. apply: stable => Hng.
  apply: (Z_bounded_above_max_nn B S Hne Hbound) => -[m [Hm Hmax]].
  apply: Hng; apply: Hk. exists m; split; last exact: (Hbound m Hm).
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
  ((exists m, GLB.is_glb Z.le m S /\ B <= m) -> G) -> G.
Proof.
  move=> Hne Hbound Hk. apply: stable => Hng.
  apply: (Z_bounded_below_min_nn B S Hne Hbound) => -[m [Hm Hmin]].
  apply: Hng; apply: Hk. exists m; split; last exact: (Hbound m Hm).
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

(** From an across abstraction, a non-positive element of [S2] is
    delivered through a [Stable] continuation: the attained min when the
    low bound is finite, an element below [1] when it is [Top]. *)
Lemma across_le0_witness {G : Prop} `{Stable G}
  (l2 : WithTop.with_top Z) (S2 : ℘ Z) :
  0 ∈ γ[glbtop] l2 -> (exists c, c ∈ S2) -> IsAlpha (A:=glbtop) l2 S2 ->
  ((exists c, c ∈ S2 /\ c <= 0) -> G) -> G.
Proof.
  case: l2 => [|a] /= Hl0 Hex Ha Hk.
  - apply: (is_alpha_glbtop_top_witness S2 1 Ha) => -[c [Hc Hlt]].
    apply: Hk. exists c; split=> //; lia.
  - move: Hl0; unfold_set => Ha0.
    move: (IsAlpha_glbtop_NotTop_is_glb Z.le a S2 Ha) => Hglb.
    apply: (Z_is_glb_attained_witness a S2 Hglb) => Hain.
    apply: Hk. by exists a.
Qed.

(** Mirror: a non-negative element of [S2]. *)
Lemma across_ge0_witness {G : Prop} `{Stable G}
  (h2 : WithTop.with_top Z) (S2 : ℘ Z) :
  0 ∈ γ[lubtop] h2 -> (exists c, c ∈ S2) -> IsAlpha (A:=lubtop) h2 S2 ->
  ((exists c, c ∈ S2 /\ 0 <= c) -> G) -> G.
Proof.
  case: h2 => [|a] /= Hh0 Hex Ha Hk.
  - apply: (is_alpha_lubtop_top_witness S2 (-1) Ha) => -[c [Hc Hgt]].
    apply: Hk. exists c; split=> //; lia.
  - move: Hh0; unfold_set => Ha0.
    move: (IsAlpha_lubtop_NotTop_is_lub Z.le a S2 Ha) => Hlub.
    apply: (Z_is_lub_attained_witness a S2 Hlub) => Hain.
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
     IsAlpha (A:=itv) (WithTop.NotTop p, h2) {[ z | z ∈ S2 /\ 0 <= z ]} -> G)
  -> G.
Proof.
  move=> Hl0 Hh0 Hex Ha Hk.
  move: (Ha) => /Conjunction.is_alpha_pair_iff [Hglb Hlub].
  apply: (itv_attained_low_witness l2 h2 S2 Ha Hex) => Hatl.
  apply: (itv_attained_high_witness l2 h2 S2 Ha Hex) => Hath.
  have Hglb' := glbtop_le0_restrict l2 S2 Hl0 Hatl Hglb.
  have Hlub' := lubtop_ge0_restrict h2 S2 Hh0 Hath Hlub.
  apply: (across_le0_witness l2 S2 Hl0 Hex Hglb) => Hne_neg.
  apply: (across_ge0_witness h2 S2 Hh0 Hex Hlub) => Hne_pos.
  have Hb_neg : forall c, c ∈ {[ z | z ∈ S2 /\ z <= 0 ]} -> c <= 0
    by move=> c Hc; unfold_set in Hc; tauto.
  have Hb_pos : forall c, c ∈ {[ z | z ∈ S2 /\ 0 <= z ]} -> 0 <= c
    by move=> c Hc; unfold_set in Hc; tauto.
  have Hne_neg' : exists c, c ∈ {[ z | z ∈ S2 /\ z <= 0 ]}
    by move: Hne_neg => [c [Hc Hc0]]; exists c; unfold_set; split.
  have Hne_pos' : exists c, c ∈ {[ z | z ∈ S2 /\ 0 <= z ]}
    by move: Hne_pos => [c [Hc Hc0]]; exists c; unfold_set; split.
  apply: (Z_bounded_above_lub_witness 0 _ Hne_neg' Hb_neg) => -[m [Hlubm Hm0]].
  apply: (Z_bounded_below_glb_witness 0 _ Hne_pos' Hb_pos) => -[p [Hglbp Hp0]].
  apply: (Hk m p Hm0 Hp0).
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
  exact: (interval_lift2_monotone_alpha_complete
           Z.le Z.le Z.le z_is_unbounded z_is_unbounded_up z_le_antisymm
           f Hmono Hrefl Hrefr l2 h2 l1 h1 S2 S1
           Hatl2 Hath2 Hatl1 Hath1 Hrbl Hrbr Hral Hrar Ha2 Ha1).
Qed.

(** Best abstraction for [interval_add] on abstract sets. Derived from the
    generic [Z_interval_lift2_alpha_complete]: casing the pair operands
    makes [interval_add] and [interval_lift2 Z.add] reduce to the same
    pair, so [apply:] can unify by conversion. *)
Lemma interval_add_alpha_complete (i2 i1 : interval) (S2 S1 : ℘ Z) :
  (exists c, c ∈ S2) ->
  (exists c, c ∈ S1) ->
  binary_alpha_complete itv itv itv interval_add
    (collecting_binary_forward Z.add) i2 i1 S2 S1.
Proof.
  case: i2 => l2 h2; case: i1 => l1 h1.
  apply: (Z_interval_lift2_alpha_complete Z.add).
  - exact: Zadd_monotone_binop.
  - exact: Zadd_order_reflecting_left.
  - exact: Zadd_order_reflecting_right.
  - move=> a b; exists (b - a); lia.
  - move=> a b; exists (b - a); lia.
  - move=> a b; exists (b - a); lia.
  - move=> a b; exists (b - a); lia.
Qed.

End Interval_add.


(* opp: the unary minus. It is sound and exact, even when the interval may be bottom. *)
Section Interval_opp.

  (** * Negation and best abstraction transfer. *)
  Definition neg_bound (b : WithTop.with_top Z) : WithTop.with_top Z :=
    match b with WithTop.Top => WithTop.Top | WithTop.NotTop z => WithTop.NotTop (-z) end.

  Definition interval_opp (i : interval) : interval :=
    let (l, h) := i in (neg_bound h, neg_bound l).


  (** Opp is exact, even when the interval is bottom. *)
  Lemma interval_opp_exact:
    unary_exact itv itv interval_opp
      (collecting_forward Z.opp).
  Proof.
    move=> a1. unfold interval_opp.
    have HU:= unfold_set_equiv.
    unfold ExactlyRepresents, collecting_forward; unfold_set.
    move=> c; unfold_set.
    split.
    - move=> H.
      exists (-c); move: a1 H => [[|l] [|h]] H; unfold neg_bound in *;
                           unfold_set in H; unfold_set; simpl in *; lia.
    - move=> [c0 [H1 <-]].
      move: a1 H1 => [[|l] [|h]] H1; unfold_set in *; simpl in *; lia.
  Qed.

  (** Best abstraction transfers through Z.opp:
      if a is best for S, then opp(a) is best for {z | -z ∈ S}. *)
  Lemma best_abstraction_opp (a : interval) (S : propset Z) :
    BestAbstraction (A:=itv) a S ->
    BestAbstraction (A:=itv) (interval_opp a) {[ z | (-z) ∈ S ]}.
  Proof.
    move=> [Hsound Hopt]; apply best_abstraction_iff; split.
    - (* Soundness: (-z) ∈ S ⊆ γ(a), so z ∈ γ(opp(a)) *)
      move=> z; rewrite propset_elem_of_iff => Hz.
      { apply interval_opp_exact. unfold collecting_forward.
        unfold_set. exists (-z).
        split; [by apply Hsound | lia ]. }
    - (* Optimality: opp(b) overapproximates S, so a ⊑ opp(b) *)
      move=> b Hb.
      have Hb': Overapproximates (A:=itv) (interval_opp b) S.
      { move=> z Hz; apply interval_opp_exact. unfold collecting_forward.
        to_set in Hb. unfold_set. exists (-z).
        split.
        + apply Hb; unfold_set. by replace (- -z) with z by lia.
        + lia. }
      move: (Hopt _ Hb') => {Hsound Hopt Hb Hb'}.
      move: a b => [[|la] [|ha]] [[|lb] [|hb]] //=; try lia.
      all: rewrite /GLB.glb_is_included; lia.
  Qed.

  Lemma interval_opp_involutive (i : interval) :
    interval_opp (interval_opp i) = i.
  Proof.
    case: i => [l h] /=; case: l => [|l]; case: h => [|h] //=;
      repeat (f_equal; try lia).
  Qed.

  Lemma propset_opp_involutive (S : ℘ Z) :
    {[ z | -z ∈ {[ z' | -z' ∈ S ]} ]} ⊆⊇ S.
  Proof.
    split=> z; unfold_set => H; by replace (- -z) with z in * by lia.
  Qed.

  (** IsAlpha transports through interval_opp / Z.opp on both sides, since
      opp is an involutive bijection (concrete and abstract) and exact. *)
  Lemma is_alpha_opp_iff (a : interval) (S : ℘ Z) :
    IsAlpha (A:=itv) a S <-> IsAlpha (A:=itv) (interval_opp a) {[ z | -z ∈ S ]}.
  Proof.
    rewrite !is_alpha_iff_best_abstraction. split.
    - exact: best_abstraction_opp.
    - move/best_abstraction_opp. rewrite interval_opp_involutive => Hba.
      exact: (best_abstraction_equiv _ _ _ Hba (propset_opp_involutive _)).
  Qed.

  (** Transport α-completeness across left-argument negation. The new
      abstract function is [fun b2 b1 => interval_opp (fA (interval_opp b2) b1)];
      [fC] is unchanged but must commute with negating its left argument. *)
  Lemma binary_alpha_complete_opp_l
    (fA : interval -> interval -> interval) (fC : setop2 Z Z Z)
    (a2 a1 : interval) (S2 S1 : ℘ Z) :
    (forall T2 T1, fC {[ z | -z ∈ T2 ]} T1 ⊆⊇ {[ z | -z ∈ fC T2 T1 ]}) ->
    binary_alpha_complete itv itv itv fA fC a2 a1 S2 S1 ->
    binary_alpha_complete itv itv itv
      (fun b2 b1 => interval_opp (fA (interval_opp b2) b1)) fC
      (interval_opp a2) a1 {[ z | -z ∈ S2 ]} S1.
  Proof.
    rewrite /binary_alpha_complete => HfC Hac Ha2n Ha1.
    rewrite interval_opp_involutive.
    have Ha2 : IsAlpha (A:=itv) a2 S2.
    { have Hiff := is_alpha_opp_iff (interval_opp a2) {[ z | -z ∈ S2 ]}.
      rewrite interval_opp_involutive in Hiff.
      apply: (is_alpha_set_equiv _ _ _ (propset_opp_involutive S2)).
      exact: (proj1 Hiff Ha2n). }
    have Hres := Hac Ha2 Ha1.
    have Hres' : IsAlpha (A:=itv) (interval_opp (fA a2 a1)) {[ z | -z ∈ fC S2 S1 ]}
      by apply (is_alpha_opp_iff _ _).1.
    apply: (is_alpha_set_equiv _ _ _ _ Hres').
    split; apply HfC.
  Qed.

  (** Right-argument symmetric version. *)
  Lemma binary_alpha_complete_opp_r
    (fA : interval -> interval -> interval) (fC : setop2 Z Z Z)
    (a2 a1 : interval) (S2 S1 : ℘ Z) :
    (forall T2 T1, fC T2 {[ z | -z ∈ T1 ]} ⊆⊇ {[ z | -z ∈ fC T2 T1 ]}) ->
    binary_alpha_complete itv itv itv fA fC a2 a1 S2 S1 ->
    binary_alpha_complete itv itv itv
      (fun b2 b1 => interval_opp (fA b2 (interval_opp b1))) fC
      a2 (interval_opp a1) S2 {[ z | -z ∈ S1 ]}.
  Proof.
    rewrite /binary_alpha_complete => HfC Hac Ha2 Ha1n.
    rewrite interval_opp_involutive.
    have Ha1 : IsAlpha (A:=itv) a1 S1.
    { have Hiff := is_alpha_opp_iff (interval_opp a1) {[ z | -z ∈ S1 ]}.
      rewrite interval_opp_involutive in Hiff.
      apply: (is_alpha_set_equiv _ _ _ (propset_opp_involutive S1)).
      exact: (proj1 Hiff Ha1n). }
    have Hres := Hac Ha2 Ha1.
    have Hres' : IsAlpha (A:=itv) (interval_opp (fA a2 a1)) {[ z | -z ∈ fC S2 S1 ]}
      by apply (is_alpha_opp_iff _ _).1.
    apply: (is_alpha_set_equiv _ _ _ _ Hres').
    split; apply HfC.
  Qed.

End Interval_opp.

Section Interval_sub.

  (** Direct definition for efficient extraction. Equivalent to
      interval_add i1 (interval_opp i2), proved below. *)

  Definition sub_bound (a b : WithTop.with_top Z) : WithTop.with_top Z :=
    match a, b with
    | WithTop.Top, _ | _, WithTop.Top => WithTop.Top
    | WithTop.NotTop a, WithTop.NotTop b => WithTop.NotTop (a - b)
    end.

  Definition interval_sub (i1 i2 : interval) : interval :=
    let (l1,h1) := i1 in
    let (l2,h2) := i2 in
    (sub_bound l1 h2, sub_bound h1 l2).

  (* This allows reusing the proofs of add + opp. *)
  Local Lemma interval_sub_eq_add_opp i1 i2:
    interval_sub i1 i2 = interval_add i1 (interval_opp i2).
  Proof.
    move: i1 i2 => [[|l1] [|h1]] [[|l2] [|h2]] //=.
  Qed.

  Lemma interval_sub_sound:
    binary_overapproximation itv itv itv interval_sub
      (collecting_binary_forward Z.sub).
  Proof.
    overapproximation_proof. subst c0. rewrite interval_sub_eq_add_opp.
    apply interval_add_sound. exists c2, (-c1). repeat split; try lia.
    - exact Hc2_in_a2.
    - apply interval_opp_exact. exists c1. split; [exact Hc1_in_a1 | lia].
  Qed.

  (** Lift to non-bottom intervals. *)
  Definition nb_interval_sub :=
    non_bottom_lift_total_binary interval_sub Z.sub (Hsound:=interval_sub_sound).

  (** opp preserves non-bottom, so we can lift it to nb_interval. *)
  Lemma interval_opp_preserves_non_bottom i:
    non_bottom i -> non_bottom (interval_opp i).
  Proof. move: i => [[|l] [|h]] //=; lia. Qed.

  Definition nb_interval_opp (i : nb_interval) : nb_interval :=
    exist _ (interval_opp (`i)) (interval_opp_preserves_non_bottom _ (proj2_sig i)).

  (** Completeness: every c in γ(sub i2 i1) decomposes as c2 - c1.
      with c2 ∈ γ i2 and c1 ∈ γ i1. We reuse the interval addition
      proof.  *)
  Lemma nb_interval_sub_gamma_complete:
    binary_underapproximation nbitv nbitv nbitv nb_interval_sub
      (collecting_binary_forward Z.sub).
  Proof.
    move=> i2 i1 c0 Hc0.
    (* Rewrite to add + opp form, then decompose via add exactness *)
    rewrite gamma_nbitv_gamma_itv /= interval_sub_eq_add_opp in Hc0.
    have [Hunder _] := nb_interval_add_exact i2 (nb_interval_opp i1).
    have /= := Hunder c0 Hc0.
    unfold_set. move=> [c2 [c_opp [Hc2 [Hcopp Heq]]]].
    (* Witnesses: c2 and -c_opp, since c2 - (-c_opp) = c2 + c_opp = c0 *)
    exists c2, (-c_opp). repeat split; [exact Hc2 | | lia].
    (* -c_opp ∈ γ(i1) follows from c_opp ∈ γ(opp i1) by opp exactness *)
    rewrite gamma_nbitv_gamma_itv /= in Hcopp |- *.
    have [Hopp _] := interval_opp_exact (`i1).
    have := Hopp c_opp Hcopp. unfold_set.
    move=> [c1 [Hc1 Heq1]]. have ->: -c_opp = c1 by lia. exact Hc1.
  Qed.

  Lemma nb_interval_sub_exact:
    binary_exact nbitv nbitv nbitv nb_interval_sub
      (collecting_binary_forward Z.sub).
  Proof.
    move=> i2 i1; split.
    - apply nb_interval_sub_gamma_complete.
    - apply non_bottom_lift_sound.
  Qed.

End Interval_sub.

Inductive classification := Pos | Neg | Across.

Definition classify (i:interval) :=
  let (l,h) := i in
  match l,h with
  | WithTop.NotTop z, _ =>
      if z >=? 0 then Pos
      else match h with
           | WithTop.NotTop z' => if z' <=? 0 then Neg else Across
           | WithTop.Top => Across
           end
  | WithTop.Top, WithTop.NotTop z =>
      if z <=? 0 then Neg else Across
  | WithTop.Top, WithTop.Top => Across
  end.

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

(** Classify the divisor, and returns an interval where 0 has been
removed from the bounds. *)
Inductive divisor_classification :=
  | DivPos of interval
  | DivNeg of interval
  | DivZero
  | DivAcross.

Definition classify_divisor (i:interval) :=
  let (l,h) := i in
  match l with
  | WithTop.NotTop l' =>
      if l' >? 0 then DivPos i
      else match h with
           | WithTop.NotTop h' =>
               if h' <? 0 then DivNeg i
               else if Z.eqb l' 0 then
                      if  Z.eqb h' 0 then DivZero
                      else DivPos (WithTop.NotTop 1, h)
                    else if Z.eqb h' 0 then DivNeg (l, WithTop.NotTop (-1))
               else DivAcross
           | WithTop.Top =>
               if Z.eqb l' 0
               then DivPos (WithTop.NotTop 1, h)
               else DivAcross
           end
  | WithTop.Top =>
      match h with
       | WithTop.NotTop h' =>
           if h' <? 0 then DivNeg i
           else if Z.eqb h' 0 then DivNeg (l, WithTop.NotTop (-1))
           else DivAcross
       | WithTop.Top => DivAcross
      end
  end.

Section Interval_quot.

  (** * Collecting semantics for quotient: excludes division by zero.
      The result is empty (bottom) when all divisors are zero. *)
  Definition collecting_quot (S2 S1 : propset Z) : propset Z :=
    {[c0 | exists c2 c1, c2 ∈ S2 /\ c1 ∈ S1 /\ c1 <> 0 /\ Z.quot c2 c1 = c0]}.
  Hint Unfold collecting_quot: to_set.

  
  Section Interval_quot_pos.
    
    (** Division bound: a / b with Top handling.
      Top / b = Top (unbounded dividend -> unbounded quotient)
      a / Top = 0  (finite dividend / unbounded divisor -> 0) *)
    Definition quot_bound (a b : WithTop.with_top Z) : WithTop.with_top Z :=
      match a, b with
      | _, WithTop.Top => WithTop.NotTop 0
      | WithTop.Top, _ => WithTop.Top
      | WithTop.NotTop a, WithTop.NotTop b => WithTop.NotTop (Z.quot a b)
      end.

    (** For positive dividend [l1,h1] and strictly positive divisor [l2,h2]:
      result = [l1/h2, h1/l2]. *)
    Definition interval_quot_pos (i1 i2 : interval) : interval :=
      let (l1, h1) := i1 in
      let (l2, h2) := i2 in
      (quot_bound l1 h2, quot_bound h1 l2).


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

  (** Quarter functions: both dividend and divisor have definite sign. *)

  Definition interval_quot_neg_pos (i2 i1 : interval) : interval :=
    interval_opp (interval_quot_pos (interval_opp i2) i1).

  Definition interval_quot_pos_neg (i2 i1 : interval) : interval :=
    interval_opp (interval_quot_pos i2 (interval_opp i1)).

  Definition interval_quot_neg_neg (i2 i1 : interval) : interval :=
    interval_quot_pos (interval_opp i2) (interval_opp i1).

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

  (** Across-dividend functions: dividend crosses zero, divisor has definite sign.
      Split the dividend at 0. *)

  Definition interval_quot_across_pos (i2 i1 : interval) : interval :=
    join_itv
      (interval_quot_neg_pos (fst i2, WithTop.NotTop 0) i1)
      (interval_quot_pos (WithTop.NotTop 0, snd i2) i1).

  Definition interval_quot_across_neg (i2 i1 : interval) : interval :=
    join_itv
      (interval_quot_neg_neg (fst i2, WithTop.NotTop 0) i1)
      (interval_quot_pos_neg (WithTop.NotTop 0, snd i2) i1).

  (** Across-divisor functions: divisor crosses zero.
      Split the divisor into [l1, -1] and [1, h1], excluding 0. *)

  Definition interval_quot_pos_across (i2 i1 : interval) : interval :=
    let (l1, h1) := i1 in
    join_itv
      (interval_quot_pos_neg i2 (l1, WithTop.NotTop (-1)))
      (interval_quot_pos i2 (WithTop.NotTop 1, h1)).

  Definition interval_quot_neg_across (i2 i1 : interval) : interval :=
    let (l1, h1) := i1 in
    join_itv
      (interval_quot_neg_neg i2 (l1, WithTop.NotTop (-1)))
      (interval_quot_neg_pos i2 (WithTop.NotTop 1, h1)).

  (** Optimized across-divisor functions (moved here so across_across can use them). *)
  Definition interval_quot_pos_across_opt (i2 i1 : interval) : interval :=
    let (_, h2) := i2 in (neg_bound h2, h2).

  Definition interval_quot_neg_across_opt (i2 i1 : interval) : interval :=
    let (l2, _) := i2 in (l2, neg_bound l2).

  Definition interval_quot_across_across (i2 i1 : interval) : interval :=
    let (l2, h2) := i2 in
    join_itv
      (interval_quot_neg_across_opt (l2, WithTop.NotTop 0) i1)
      (interval_quot_pos_across_opt (WithTop.NotTop 0, h2) i1).

  Definition interval_quot_full (i2 i1 : interval) : interval :=
    match classify_divisor i1 with
    | DivZero => bottom
    | DivPos i1_san =>
        match classify i2 with
        | Pos    => interval_quot_pos i2 i1_san
        | Neg    => interval_quot_neg_pos i2 i1_san
        | Across => interval_quot_across_pos i2 i1_san
        end
    | DivNeg i1_san =>
        match classify i2 with
        | Pos    => interval_quot_pos_neg i2 i1_san
        | Neg    => interval_quot_neg_neg i2 i1_san
        | Across => interval_quot_across_neg i2 i1_san
        end
    | DivAcross =>
        match classify i2 with
        | Pos    => interval_quot_pos_across i2 i1
        | Neg    => interval_quot_neg_across i2 i1
        | Across => interval_quot_across_across i2 i1
        end
    end.

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

Require Import Extraction.
Extraction Language OCaml.
Require Import ExtrOcamlBasic.

Extraction Inline non_bottom_lift_total_binary.
(* Extraction Inline ad_car abs_car abstract_domain_to_abstraction. *)
(* Extraction Inline WithTop.lift2. *)

Separate Extraction interval_add nb_interval_add.


Section Interval_mul.

  Definition bound_mul a b :=
    match a, b with
    | WithTop.NotTop 0, _ | _, WithTop.NotTop 0 => WithTop.NotTop 0
    | WithTop.NotTop x, WithTop.NotTop y => WithTop.NotTop (x * y)
    | _,_ => WithTop.Top
    end.

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

  Definition interval_mul_opt (i2 i1: interval) : interval :=
    let (l1,h1) := i1 in
    let (l2,h2) := i2 in
    let m := bound_mul in
    match classify i1, classify i2 with
    | Pos, Pos => (m l1 l2, m h1 h2)
    | Neg, Neg => (m h1 h2, m l1 l2)
    | Pos, Neg => (m h1 l2, m l1 h2)
    | Neg, Pos => (m l1 h2, m h1 l2)
    | Pos, Across => (m h1 l2, m h1 h2)
    | Across, Pos => (m l1 h2, m h1 h2)
    | Neg, Across => (m l1 h2, m l1 l2)
    | Across, Neg => (m h1 l2, m l1 l2)
    | Across, Across =>
        (min_opt (m l1 h2) (m h1 l2), max_opt (m l1 l2) (m h1 h2))
    end.

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

(** * Interval comparison: abstract Z.leb *)

Section Interval_leb.

(** Whether Z.leb c1 c2 = true is possible: need c1 ≤ c2,
    i.e. the lower bound of i1 ≤ the upper bound of i2. *)
Definition may_be_true_leb (l2 h1 : WithTop.with_top Z) : bool :=
  match l2, h1 with
  | WithTop.Top, _ => true
  | _, WithTop.Top => true
  | WithTop.NotTop l2', WithTop.NotTop h1' => Z.leb l2' h1'
  end.

(** Whether Z.leb c1 c2 = false is possible: need c2 < c1,
    i.e. the upper bound of i1 > the lower bound of i2. *)
Definition may_be_false_leb (h2 l1 : WithTop.with_top Z) : bool :=
  match h2, l1 with
  | WithTop.Top, _ => true
  | _, WithTop.Top => true
  | WithTop.NotTop h2', WithTop.NotTop l1' => negb (Z.leb h2' l1')
  end.

Definition interval_leb (i2 i1 : interval) : quadrivalent :=
  let (l2, h2) := i2 in
  let (l1, h1) := i1 in
  to_quadrivalent (may_be_true_leb l2 h1) (may_be_false_leb h2 l1).

Definition nbinterval_leb (i2 i1 : nb_interval) : quadrivalent := interval_leb (`i2) (`i1).


Lemma nbinterval_leb_exact:
  binary_exact nbitv nbitv qv nbinterval_leb
    (collecting_binary_forward Z.leb).
Proof.
  move=> [[l2 h2] P2] [[l1 h1] P1]. unfold nbinterval_leb,interval_leb. simpl.
  unfold ExactlyRepresents. to_set. 
  have HU := unfold_set_equiv. unfold_set. clear HU.
  apply non_bottom_non_empty in P1. destruct P1 as [w1 H1].
  apply non_bottom_non_empty in P2. destruct P2 as [w2 H2].
  move => c. case: c.
  - rewrite to_quadrivalent_true. unfold may_be_true_leb.
    setoid_rewrite Z.leb_le.
    destruct l2 as [|l2].
    + split => //; move => _.
      exists (Z.min w2 w1), w1.
      unfold_set in H1; simpl in H1.
      repeat split; try (tauto||lia).
      * destruct h2; simpl => //. unfold_set. unfold_set in H2; simpl in H2. lia.
    + destruct h1 as [|h1].
      * split => //; move => _.
        unfold_set in H2; simpl in H2.
        exists w2, (Z.max w2 w1). simpl. repeat split; try (tauto||lia).
        -- destruct l1; simpl => //. unfold_set in H1; simpl in H1. unfold_set. lia.
      * setoid_rewrite Z.leb_le. simpl.
        split. move=> Hl2l1.
        -- exists l2,h1. unfold_set. repeat split => //.
           ++ lia.
           ++ destruct h2 => //; simpl. unfold_set in H2. simpl in H2. unfold_set. lia.
           ++ destruct l1 => //. unfold_set. unfold_set in H1; simpl in H1. lia.
           ++ reflexivity.
        -- move => [c2 [c1 H]]. unfold_set in H. lia.
  - rewrite to_quadrivalent_false. unfold may_be_false_leb.
    destruct h2 as [|h2].
    + split => //; move => _.
      exists (Z.max w2 (w1 + 1)), w1. unfold_set. repeat split.
      * destruct l2; unfold_set; simpl => //. unfold_set in H2; simpl in H2. lia.
      * destruct l1; unfold_set; simpl => //. unfold_set in H1; simpl in H1. lia.
      * unfold_set. unfold_set in H1. simpl in H1. tauto.
      * apply Z.leb_gt. lia.
    + destruct l1 as [|l1].
      (* l1 = Top, h2 = NotTop h2 *)
      * split => //; move => _.
        exists w2, (Z.min w2 w1 - 1). repeat split.
        all: destruct l2; destruct h1;
             unfold_set in H2; unfold_set in H1; unfold_set;
             simpl in *; try tauto; try lia.
        all: try (apply Z.leb_gt; lia).
      (* l1 = NotTop l1, h2 = NotTop h2 *)
      * split.
        -- case: (Z.leb_spec h2 l1) => // Hh2l1 _.
           exists h2, l1.
           destruct l2; destruct h1;
             unfold_set in H2; unfold_set in H1; unfold_set;
             simpl in *; repeat split; try tauto; try lia.
           all: apply Z.leb_gt; lia.
        -- move => [c2 [c1 H]].
           destruct l2; destruct h1;
             unfold_set in H; simpl in H.
           all: apply negb_true_iff; apply Z.leb_gt; lia.
Qed.

End Interval_leb.
