(* Z_interval.v - Interval arithmetic for integers *)
(* Noth: there are intervals in mathcomp; we could reuse their notations. *)

(* STATUS (ladder: sound < best < exact < α-complete).

   All transfer functions now live in Transfer_function/ZInterval/; what is
   left here is the abstraction itself, the generic α-machinery the operation
   proofs share, and the [classify] / [classify_divisor] sign dispatchers.
     opp:  exact                      -- OppTheory.v
     add:  sound + best (α-complete)  -- AddTheory.v
     sub:  sound + exact (non-bottom) -- AddTheory.v
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

