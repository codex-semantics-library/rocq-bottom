(** This file drives the extraction of quadrivalent to ML code. *)

Require Import ssrbool ssreflect.
Require Import Abstraction autoreflect AbstractLattice.
Generalizable All Variables.

(* Optional: Load the Extraction library *)
Require Import Extraction.
Extraction Language OCaml.
Require Import ExtrOcamlBasic.
(* Extract Inlined Constant andb => "(&&)". *)
(* Extract Inlined Constant orb  => "(||)". *)
(* Extract Inlined Constant negb => "not". *)
(* Map Coq's prod to OCaml's native tuple *)
(* Extract Inductive prod => "( * ) " [ "(,)" ]. *)


Extraction Inline ssrbool.is_left.

Module Concrete := Datatypes.

Require Import QuadrivalentComp.
Module QuadrivalentCheck <: ABSTRACT_DOMAIN := QuadrivalentTheory.
(* Separate Extraction QuadrivalentTheory.t. *)
Separate Extraction QuadrivalentTheory.t.

Extraction Inline QuadrivalentTheory.dec.
Module QuadrivalentLatticeCheck <: ABSTRACT_LATTICE := QuadrivalentTheory.
Separate Extraction QuadrivalentTheory.join QuadrivalentTheory.meet
  QuadrivalentTheory.equal QuadrivalentTheory.is_included. 

Require Import SvaQuadrivalent.
Separate Extraction SvaQuadrivalent.Boolean_Forward SvaQuadrivalent.Boolean_Backward.

(* From QuickChick Require Import QuickChick. *)
(* Import QcDefaultNotation. *)

(* 1. Show: So QuickChick can print "Counterexample: QTrue" *)
(* Instance show_quad : Show quadrivalent := {| *)
(*   show q := match q with *)
(*             | QBottom => "Bot" | QTrue => "T" *)
(*             | QFalse => "F" | QTop => "Top" end *)
(* |}. *)

(* 2. Gen: Randomly pick one of the four constructors *)
(* Instance gen_quad : Gen quadrivalent := *)
(*   elems [QBottom; QTrue; QFalse; QTop]. *)

(* This automatically creates Gen, Show, and Shrink *)

(* Derive (Arbitrary, Show) for quadrivalent. *)

(* (* 3. Shrink: If QTop fails, try to see if QTrue also fails (minimizing) *) *)
(* Instance shrink_quad : Shrink quadrivalent := {| *)
(*                                                shrink q := match q with *)
(*                                                            | QTop => [QTrue; QFalse; QBottom] *)
(*                                                            | QTrue | QFalse => [QBottom] *)
(*                                                            | QBottom => [] *)
(*                                                            end *)
(*                                              |}. *)


(* (* QuickChick abs_negb_exact. *) *)
