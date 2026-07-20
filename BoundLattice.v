Require Import Corelib.Classes.CRelationClasses.
Require Import BoundAbstraction.
Require Import Abstraction.
Require Import AbstractLattice.
Require Import AbstractionCombination.
Require Import ssreflect.
Generalizable All Variables.

(* When we have a concrete lattice following a preorder le, then we
   can turn it into lattices of bounds and intervals.

 *)


(* The lattice based on the ordering relation le. *)
Structure ConcreteLattice {A:Type} :=
  BuildConcreteLattice {
      cl_car :> Type;

      cl_le: A -> A -> Prop;
      cl_equiv: A -> A -> Prop;
      cl_min: A -> A -> A;
      cl_max: A -> A -> A;
      
      cl_Hpre: PreOrder cl_le;
      (* Equiv is the equivalence relation induced by the le preorder. *)
      cl_equiv_spec: forall a1 a2, cl_equiv a1 a2 <-> cl_le a1 a2 /\ cl_le a2 a1;
      (* min is a lowerbound. *)
      cl_min_is_lb_l: forall a1 a2, cl_le (cl_min a1 a2) a1;
      cl_min_is_lb_r: forall a1 a2, cl_le (cl_min a1 a2) a2;
      (* min is the greatest lower bound. *)
      cl_min_is_glb: forall a1 a2 c, cl_le c a1 -> cl_le c a2 -> cl_le c (cl_min a1 a2);

      (* max is an upper bound. *)
      cl_max_is_ub_l: forall a1 a2, cl_le a1 (cl_max a1 a2);
      cl_max_is_ub_r: forall a1 a2, cl_le a2 (cl_max a1 a2);
      (* max is the lowest upper bound. *)
      cl_max_is_lub: forall a1 a2 c, cl_le a1 c -> cl_le a2 c -> cl_le (cl_max a1 a2) c;
    }.

(** Make record projections reduce as soon as possible. *)
Global Arguments cl_le {_} !_  / .
Global Arguments cl_min {_} !_  / .
Global Arguments cl_max {_} !_  / .
Global Arguments cl_equiv {_} !_ / .

Module GLB. Section GLB.

  (** ** GLB Abstract lattice. *)

  (* We define the lattice when the glb is min, lub is max, and
     equivalence relation is the one induced by the le preorder. *)
  Context {A:Type} `(CL:@ConcreteLattice A).

  Existing Instance cl_Hpre.

  Let le := cl_le CL.
  Let equiv := cl_equiv CL.
  Let min := cl_min CL.
  Let max := cl_max CL.
  Let abs := BoundAbstraction.GLB.abs le.
  Let γ_glb := BoundAbstraction.GLB.γ_glb le.
  Let glb_is_included := BoundAbstraction.GLB.glb_is_included le.
  Let Hpre := (cl_Hpre CL).
  Existing Instance Hpre.
  Let ad : abstract_domain A := @BoundAbstraction.GLB.ad A le (cl_Hpre CL).

  Program Instance glb_ajsl_laws: @abstract_join_semilattice_laws A ad min equiv.
  Next Obligation.
    hnf. apply cl_equiv_spec in H. tauto.
  Qed.
  Next Obligation.
    apply cl_min_is_lb_l.
  Qed.
  Next Obligation.
    apply cl_min_is_lb_r.
  Qed.
  Definition al : abstract_lattice A := BuildAbstractLattice ad min max equiv glb_ajsl_laws.
  Instance GLB_JoinIsLUB: JoinIsLUB al.
  Proof.
    move=> a1 a2 c H1 H2. apply cl_min_is_glb; done.
  Qed.

End GLB. End GLB.

Module LUB. Section LUB.

  (** ** LUB Abstract lattice. *)

  (* Dual of GLB: join is max, meet is min. The abstract order
     matches the concrete order (no inversion). *)
  Context {A:Type} `(CL:@ConcreteLattice A).

  Existing Instance cl_Hpre.

  Let le := cl_le CL.
  Let equiv := cl_equiv CL.
  Let min := cl_min CL.
  Let max := cl_max CL.
  Let abs := BoundAbstraction.LUB.abs le.
  Let γ_lub := BoundAbstraction.LUB.γ_lub le.
  Let lub_is_included := BoundAbstraction.LUB.lub_is_included le.
  Let Hpre := (cl_Hpre CL).
  Existing Instance Hpre.
  Let ad : abstract_domain A := @BoundAbstraction.LUB.ad A le (cl_Hpre CL).

  Program Instance lub_ajsl_laws: @abstract_join_semilattice_laws A ad max equiv.
  Next Obligation.
    hnf. apply cl_equiv_spec in H. tauto.
  Qed.
  Next Obligation.
    apply cl_max_is_ub_l.
  Qed.
  Next Obligation.
    apply cl_max_is_ub_r.
  Qed.
  Definition al : abstract_lattice A := BuildAbstractLattice ad max min equiv lub_ajsl_laws.
  Instance LUB_JoinIsLUB: JoinIsLUB al.
  Proof.
    move=> a1 a2 c H1 H2. apply cl_max_is_lub; done.
  Qed.

End LUB. End LUB.

Module GLBUnbounded. Section GLBUnbounded.

  (** ** GLBUnbounded Abstract lattice (GLB with Top). *)

  (* The GLB lattice extended with a Top element for unbounded sets.
     Now simply defined as WithTop.al applied to GLB.al. *)
  Context {A:Type} `(CL:@ConcreteLattice A).

  Definition al : abstract_lattice A := WithTop.al (GLB.al CL).
  Instance GLBUnbounded_JoinIsLUB: JoinIsLUB al.
  Proof. exact (WithTop.WithTop_JoinIsLUB (GLB.al CL) (HLUB:=GLB.GLB_JoinIsLUB CL)). Qed.

End GLBUnbounded. End GLBUnbounded.


Module LUBUnbounded. Section LUBUnbounded.

  (** ** LUBUnbounded Abstract lattice (LUB with Top). *)

  (* The LUB lattice extended with a Top element for unbounded sets.
     Now simply defined as WithTop.al applied to LUB.al. *)
  Context {A:Type} `(CL:@ConcreteLattice A).

  Definition al : abstract_lattice A := WithTop.al (LUB.al CL).
  Instance LUBUnbounded_JoinIsLUB: JoinIsLUB al.
  Proof. exact (WithTop.WithTop_JoinIsLUB (LUB.al CL) (HLUB:=LUB.LUB_JoinIsLUB CL)). Qed.

End LUBUnbounded. End LUBUnbounded.


Module Interval. Section Interval.

  (** ** Interval Abstract lattice (bounded, unreduced product). *)

  (* An interval [glb, lub] is a conjunction of a GLB and a LUB lattice.
     This is an unreduced product: no check that glb <= lub. *)
  Context {A:Type} `(CL:@ConcreteLattice A).

  Definition al : abstract_lattice A := Conjunction.al (GLB.al CL) (LUB.al CL).
  Instance Interval_JoinIsLUB: JoinIsLUB al.
  Proof.
    exact (Conjunction.Conjunction_JoinIsLUB (GLB.al CL) (LUB.al CL)
             (HLUB_A:=GLB.GLB_JoinIsLUB CL) (HLUB_B:=LUB.LUB_JoinIsLUB CL)).
  Qed.

End Interval. End Interval.


Module IntervalUnbounded. Section IntervalUnbounded.

  (** ** IntervalUnbounded Abstract lattice (unbounded, unreduced product).

      The type/order/γ definitions, non_bottom, and gammaE_leinf live in
      BoundAbstraction.IntervalUnbounded (no lattice structure needed).
      This module adds the abstract-lattice structure (join/meet) and the
      ExactOrder proof, which require min/max from ConcreteLattice. *)
  Context {A:Type} `(CL:@ConcreteLattice A).

  Let le  := cl_le CL.
  Let min := cl_min CL.
  Let max := cl_max CL.
  Existing Instance cl_Hpre.

  (** Re-export the preorder-only definitions from BoundAbstraction. *)
  Definition interval   := @BoundAbstraction.IntervalUnbounded.interval A.
  Definition non_bottom := @BoundAbstraction.IntervalUnbounded.non_bottom A le.
  Definition nb_interval := @BoundAbstraction.IntervalUnbounded.nb_interval A le.

  Lemma non_bottom_non_empty (inhabited_witness : A) :
    forall i : interval, non_bottom i <-> exists c, c ∈ γ[BoundAbstraction.IntervalUnbounded.ad le] i.
  Proof. exact (BoundAbstraction.IntervalUnbounded.non_bottom_non_empty le inhabited_witness). Qed.

  Lemma gammaE_leinf (lo hi : WithTop.with_top A) (c : A) :
    c ∈ γ[BoundAbstraction.IntervalUnbounded.ad le] (lo, hi) <->
    GLBUnbounded.leinf le lo (WithTop.NotTop c) /\
    LUBUnbounded.leinf le (WithTop.NotTop c) hi.
  Proof. exact (BoundAbstraction.IntervalUnbounded.gammaE_leinf le lo hi c). Qed.

  (** The abstract lattice (adds join/meet on top of the abstract domain). *)
  Definition al : abstract_lattice A := Conjunction.al (GLBUnbounded.al CL) (LUBUnbounded.al CL).

  Instance IntervalUnbounded_JoinIsLUB: JoinIsLUB al.
  Proof.
    exact (Conjunction.Conjunction_JoinIsLUB (GLBUnbounded.al CL) (LUBUnbounded.al CL)
             (HLUB_A:=GLBUnbounded.GLBUnbounded_JoinIsLUB CL)
             (HLUB_B:=LUBUnbounded.LUBUnbounded_JoinIsLUB CL)).
  Qed.

  Section Inhabited.
    Context (inhabited_witness : A).

    (** Non-empty intervals have ExactOrder when each bound does.
        Uses min c w / max c w to clamp into the intersection, then
        lifts back via upward/downward-closedness. Note that this
        means that we cannot move this proof to Boundabstraction
        alone; we need meet/join (min/max) to exist. *)
    Let glbtop := GLBUnbounded.al CL.
    Let lubtop := LUBUnbounded.al CL.

    Instance nonempty_exact_order
      (HEG: ExactOrder glbtop)
      (HEL: ExactOrder lubtop):
      ExactOrder (NonEmpty.ad al non_bottom).
    Proof using inhabited_witness.
      move=> [[l2 h2] P2] [[l1 h1] P1]. split.
      - apply sound_order.
      - rewrite /(_ ⊑γ[NonEmpty.ad al non_bottom] _)
                /(_ ⊑[NonEmpty.ad al non_bottom] _)
                /Conjunction.is_included.
        simpl. move=> H.
        have [w [Hwl Hwh]] := proj1 (non_bottom_non_empty inhabited_witness (l2,h2)) P2.
        have [Hw1 Hw2] := H w (conj Hwl Hwh).
        (** Proof idea (clamping witness + transitivity):
            Given: γ(l₂,h₂) ⊆ γ(l₁,h₁).  We must prove l₁ ≤ l₂
            and h₂ ≤ h₁.  For an arbitrary c, clamp it toward the
            witness w (where l₂ ≤ w ≤ h₂) to land inside the interval:
            - GLB:  min(c,w) ∈ [l₂,h₂] ⊆ [l₁,h₁], so l₁ ≤ min(c,w) ≤ c.
            - LUB:  max(c,w) ∈ [l₂,h₂] ⊆ [l₁,h₁], so c ≤ max(c,w) ≤ h₁.
            Each step is pure transitivity on the concrete order. *)
        split.
        + (* GLB: l1 ≤ min(c,w) ≤ c *)
          apply HEG. move=> c Hcl2.
          have Hmin_l : min c w ∈ γ[glbtop] l2.
          { destruct l2; simpl in *; [done|].
            unfold_set. apply cl_min_is_glb. exact: Hcl2. exact: Hwl. }
          have Hmin_h : min c w ∈ γ[lubtop] h2.
          { destruct h2; simpl in *; [done|].
            unfold_set in Hwh. unfold_set.
            etransitivity; [apply: cl_min_is_lb_r | exact: Hwh]. }
          have [Hmin1 _] := H _ (conj Hmin_l Hmin_h).
          destruct l1; simpl in *; [done|].
          unfold_set in Hmin1. unfold_set.
          etransitivity; [exact: Hmin1 | apply: cl_min_is_lb_l].
        + (* LUB: c ≤ max(c,w) ≤ h1 *)
          apply (proj2 (HEL h2 h1)). move=> c Hch2.
          have Hmax_h : max c w ∈ γ[lubtop] h2.
          { destruct h2; simpl in *; [done|].
            unfold_set. apply cl_max_is_lub; assumption. }
          have Hmax_l : max c w ∈ γ[glbtop] l2.
          { destruct l2; simpl in *; [done|].
            unfold_set in Hwl. unfold_set.
            etransitivity; [exact: Hwl | apply: cl_max_is_ub_r]. }
          have [_ Hmax2] := H _ (conj Hmax_l Hmax_h).
          destruct h1; simpl in *; [done|].
          unfold_set in Hmax2. unfold_set.
          etransitivity; [apply: cl_max_is_ub_l | exact: Hmax2].
    Qed.
  End Inhabited.

End IntervalUnbounded. End IntervalUnbounded.

