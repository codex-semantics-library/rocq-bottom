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
From RocqBottom Require Import ZInterval ZIntervalTheory ZIntervalAPI.
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

(* Two rules govern the root list below.

   One command. [Separate Extraction] translates every module reachable from its
   roots, overwriting what is already there rather than adding to it. To avoid
   this, we extract everything using a single command.

   Qualified names only. Roots are resolved in this file's scope, where several
   modules are imported at once, and a bare name defined by two modules is not
   an ambiguity error: the most recent [Import] wins.  A root written [join]
   would therefore let the [Require] order above pick, silently, between
   [Quadrivalent]'s, [ZInterval]'s and [ZIntervalAPI]'s. *)
Separate Extraction
  (* Quadrivalent: carrier, and lattice operations. *)
  Quadrivalent.quadrivalent
  Quadrivalent.join Quadrivalent.meet Quadrivalent.equiv
  Quadrivalent.is_included Quadrivalent.singleton
  Quadrivalent.to_quadrivalent
  (* QuadrivalentOps: boolean transfer functions. *)  
  QuadrivalentOps.Boolean_Forward QuadrivalentOps.Boolean_Backward

  (* ZInterval: carrier and lattice operations. Pulled by ZIntervalAPI. *)

  (* ZIntervalAPI: combines computations and proofs in a single API conforming
     to NONEMPTY_ABSTRACT_LATTICE. Members are listed one by one on purpose:
     rooting the whole module also extracts [gamma_ne]/[gamma_pe] snf and
     dependencies. *)
  ZIntervalAPI.non_empty ZIntervalAPI.possibly_empty
  ZIntervalAPI.singleton ZIntervalAPI.is_included
  ZIntervalAPI.is_non_empty ZIntervalAPI.to_non_empty
  ZIntervalAPI.equiv ZIntervalAPI.join ZIntervalAPI.meet

  (* ZIntervalOps: interval forward transfer functions. *)
  ZIntervalOps.interval_leb ZIntervalOps.interval_opp
  ZIntervalOps.interval_add ZIntervalOps.interval_sub
  ZIntervalOps.interval_mul ZIntervalOps.interval_eqb
  ZIntervalOps.interval_quot.

  
  (* Transfer-functions with proper interface, on the nb_interval
     carrier. Rooting the whole module is enough: it emits a flat top-level
     API.ml, and every definition in API.v belongs to the exported interface. *)
  (* API *)


