(** extract.v - The extraction driver: what to extract.

    There is one driver for the whole project. Rocq's [Separate Extraction]
    emits every module in a root's closure into that extraction's own output
    directory, so per-domain drivers would give each library a private copy of
    [ZInterval.ml] and OCaml would treat the copies as unrelated types. The
    cross-module references that make the output a graph — [API] opening
    [ZIntervalOps] — also exist only within a single call.

    This prelude is compiled by dune in its own DuneExtraction namespace, so
    RocqBottom modules are required with an explicit [From RocqBottom] prefix
    (the bare names used inside the theory do not resolve here).

    The output lands in _build and is distributed to the library directories by
    their (copy_files) — see ../../dune. *)

From Stdlib Require Import ssrbool ssreflect.
From RocqBottom Require Import Abstraction autoreflect AbstractLattice.
Generalizable All Variables.

Require Import Extraction.
Extraction Language OCaml.
From RocqBottomExtr Require Import PrimitiveExtraction.

Extraction Inline ssrbool.is_left.

Module Concrete := Datatypes.

From RocqBottom Require Import Quadrivalent.
From RocqBottom Require Import ZInterval ZIntervalTheory.
From RocqBottom Require Import Transfer_function.Quadrivalent.QuadrivalentOps.
From RocqBottom Require Import Transfer_function.ZInterval.ZIntervalOps.
From RocqBottom Require Import Transfer_function.ZInterval.API.


(** * Generic inlining

    [proj1_sig] is how sigmatypes reach the underlying type. *)
Extraction Inline proj1_sig.

(** * Quadrivalent

    [equiv] goes through [dec], a [decide equality] sumbool. Inlining it
    and [ssrbool.is_left] turns the pair into a plain boolean test at the
    call site. *)
Extraction Inline Quadrivalent.dec.

(** * QuadrivalentOps

    [Boolean_Forward]/[Boolean_Backward] are aliases for the raw
    definitions, so naming the modules as roots pulls both into the output
    and the [.mli] exposes [abs_andb], [impl_backward_abs_andb],
    [refine_true] and the rest alongside the interface. Inlining the
    aliased definitions moves each body into the module member that names
    it, leaving the two modules as the whole signature. [refine_*] go too
    — one-line [option] wrappers, used only from the backward bodies being
    inlined. *)
Extraction Inline
  QuadrivalentOps.abs_negb QuadrivalentOps.abs_andb
  QuadrivalentOps.abs_orb  QuadrivalentOps.abs_xorb
  QuadrivalentOps.impl_backward_abs_negb QuadrivalentOps.impl_backward_abs_andb
  QuadrivalentOps.impl_backward_abs_orb  QuadrivalentOps.impl_backward_abs_xorb
  QuadrivalentOps.refine_bottom QuadrivalentOps.refine_true
  QuadrivalentOps.refine_false.

(** * ZInterval

    Zinterval has two layers: bound-level helpers, and interval-level. Only the interval
    layer is interface, so inlining them leaves [ZInterval.mli] with the
    abstraction's operations and nothing else. *)
Extraction Inline
  ZInterval.glbtop_is_includedb ZInterval.lubtop_is_includedb
  ZInterval.join_lb  ZInterval.join_ub
  ZInterval.meet_lb  ZInterval.meet_ub
  ZInterval.bound_equal
  ZInterval.glb_gammab ZInterval.lub_gammab.

(* Everything is extracted by ONE [Separate Extraction]. Each call rewrites
   from scratch every module reachable from its own roots, so two calls
   touching the same module do not merge: the second overwrites the first. *)
Separate Extraction
  (* Quadrivalent: carrier, and lattice operations. *)
  Quadrivalent.quadrivalent
  Quadrivalent.join Quadrivalent.meet Quadrivalent.equiv
  Quadrivalent.is_included Quadrivalent.singleton
  Quadrivalent.to_quadrivalent
  (* QuadrivalentOps: boolean transfer functions. *)  
  QuadrivalentOps.Boolean_Forward QuadrivalentOps.Boolean_Backward

  ZInterval.interval ZInterval.nb_interval

