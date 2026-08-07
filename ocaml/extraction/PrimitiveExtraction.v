(** PrimitiveExtraction.v - Rocq's number types, mapped onto zarith.

    The reusable half of extraction: [Z], [positive], [N], [nat], [bool] and
    their operations. *What* to extract is the driver's job
    (driver/extract.v), which Requires this file and brings its own
    [Extraction Language], [Separate Extraction] and [Extraction Inline]. A
    module of its own because a [coq.extraction] prelude can only [Require]
    from a theory in an *ancestor* directory (../dune, driver/dune).

    Not [ExtrOcamlZBigInt]: it targets [Big_int_Z.big_int], zarith's legacy
    shim, and realizes only floor division, leaving [Z.quot] as the Rocq
    binary algorithm. On [API.div], 200k divisions over 39-digit bounds:
    29.5s, against 0.019s once [Z.quot] is realized.

    Four rules.

    1. Realizing a constant hides its body, but extraction still walks it for
       dependencies, so follow a realization down: [Z.quot] is not done until
       [N.pos_div_eucl] is.

    2. No *copied* module may end up with [open BinInt]: that means an
       unrealized [Z] operation, and [BinInt]'s inner [module Z] would shadow
       zarith's. The OCaml build fails first, which is the alarm. Uncopied
       files ([PosDef.ml], ...) may keep their dead code.

    3. Realize only what the current roots reach, representations included;
       the rest stays commented for the domains not yet extracted (KnownBits
       the bits, ZIntervalCongruence the floor division, ZCongruence [Z.gcd]
       and [Z.quot]). To re-derive the live set: comment one out, rebuild,
       see whether the generated OCaml moves.

    4. Spell [Pos]/[N] realizations [PosDef.Pos.add], never [Pos.add]: the
       short names are [BinPos]/[BinNat] aliases and a realization on an
       alias is silently ignored. Each operation also exists twice, in
       [Corelib]'s [PosDef]/[NatDef]/[IntDef] and [Stdlib]'s
       [BinPos]/[BinNat]/[BinInt]. *)

From Stdlib Require Import ZArith NArith Extraction.
(* Primitives.v holds the operations that exist only to be realized here:
   they carry the precondition that lets a zarith primitive be named
   directly, instead of a guard standing in for Rocq's totality. *)
From RocqBottom Require Import Primitives.

(** Keep any Rocq module from being written to [Z.ml]/[N.ml]/[Q.ml], where
    it would shadow zarith's. *)
Extraction Blacklist Z N Q.

(** * Basic types

    Upstream's [ExtrOcamlBasic], spelled out so the whole inherited mapping
    is in one file and a Stdlib update cannot add to it silently. [sumbool]
    to [bool] is what makes a [decide equality] free, given [ssrbool.is_left]
    inlined in the driver. These nine are the exception to rule 3: [unit],
    [list] and [sumor] are unreached, but a mapping inherited in pieces is
    worse than one inherited whole. *)

Extract Inductive bool => bool [ true false ].
Extract Inductive option => option [ Some None ].
Extract Inductive sumbool => bool [ true false ].
(** The "" is upstream's hack: nicer output than "(,)". *)
Extract Inductive prod => "( * )" [ "" ].
Extract Inductive unit => unit [ "()" ].
Extract Inductive list => list [ "[]" "( :: )" ].
Extract Inductive sumor => option [ Some None ].

(** * Representation

    We want to extract Rocq's [Z] to zarith's [Z.t]. We also need [positive],
    because every nonzero literal is built from it ([1] is [Zpos xH], [5] is
    [Zpos (xI (xO xH))]). We want [Zpos] to cost nothing, which means it must
    be the identity ("" here) — and that is what forces [positive] to [Z.t]. *)

Extract Inductive positive => "Z.t"
 [ "(fun p -> Z.succ (Z.shift_left p 1))"
   "(fun p -> Z.shift_left p 1)"
   "Z.one" ]
 "(fun f2p1 f2p f1 p ->
  if Z.leq p Z.one then f1 ()
  else if Z.is_even p then f2p (Z.shift_right p 1)
  else f2p1 (Z.shift_right p 1))".


Extract Inductive Z => "Z.t"
 [ "Z.zero" "" "Z.neg" ]
 "(fun f0 fp fn z -> let s = Z.sign z in
  if s = 0 then f0 () else if s > 0 then fp z else fn (Z.neg z))".

(* Extract Inductive N => "Z.t"
 [ "Z.zero" "" ]
 "(fun f0 fp n -> if Z.sign n <= 0 then f0 () else fp n)". *)
(** * [Z] operations

    Zarith raises where Rocq's [Z] is total ([_ / 0 = 0], [_ mod 0] is the
    dividend, [log2 _ = 0] below 1), so those realizations guard. To avoid this,
    we don't translate these operators, and use and redefine partial ones
    instead, proving in Rocq that their uses is safe (and we need no guard). *)
Extract Inlined Constant Z.add => "Z.add".
Extract Inlined Constant Z.sub => "Z.sub".
Extract Inlined Constant Z.mul => "Z.mul".
Extract Inlined Constant Z.opp => "Z.neg".
(* Extract Inlined Constant Z.succ => "Z.succ". *)
(* Extract Inlined Constant Z.pred => "Z.pred". *)
(* Extract Inlined Constant Z.abs => "Z.abs". *)
(* Extract Inlined Constant Z.sgn => "(fun x -> Z.of_int (Z.sign x))". *)
Extract Inlined Constant Z.min => "Z.min".
Extract Inlined Constant Z.max => "Z.max".
(* Extract Inlined Constant Z.double => "(fun x -> Z.shift_left x 1)". *)
(* Extract Inlined Constant Z.succ_double => "(fun x -> Z.succ (Z.shift_left x 1))". *)
(* Extract Inlined Constant Z.pred_double => "(fun x -> Z.pred (Z.shift_left x 1))". *)
(** [pos_sub p q] is [Zpos p - Zpos q]. *)
(* Extract Inlined Constant Z.pos_sub => "Z.sub". *)

(** Non-negative, and [gcd 0 0 = 0] on both sides. For ZCongruence. *)
(* Extract Inlined Constant Z.gcd => "Z.gcd". *)

Extract Inlined Constant Z.eqb => "Z.equal".
Extract Inlined Constant Z.eq_dec => "Z.equal".
(** [sumbool] is [bool], so a decision realizes like the matching test.
    [Z_lt_dec] is reached by [classify_divisor], which decides rather than
    tests so each branch carries its constructor's order fact. *)
Extract Inlined Constant Z_lt_dec => "Z.lt".
Extract Inlined Constant Z_lt_le_dec => "Z.lt".
Extract Inlined Constant Z.leb => "Z.leq".
Extract Inlined Constant Z.ltb => "Z.lt".
Extract Inlined Constant Z.geb => "Z.geq".
(* Extract Inlined Constant Z.gtb => "Z.gt". *)
(* Extract Inlined Constant Z.even => "(fun x -> Z.is_even x)". *)
(* Extract Inlined Constant Z.odd => "(fun x -> Z.is_odd x)". *)
(** ** Division

    Truncated (C99): zarith's [Z.div]/[Z.rem] round toward zero and give the
    remainder the dividend's sign, like Rocq's [Z.quot]/[Z.rem].
    [Primitives.quot_non_zero] is [Z.quot] with the divisor known non-zero; the
    proof erases, so it needs no guard, with nothing left to get wrong in the
    string. We explicitly do not provide a translation for Z.quot/rem/quotrem *)
Extract Inlined Constant quot_non_zero => "Z.div".
(* Extract Inlined Constant Z.quot => "(fun x y -> if Z.equal y Z.zero then Z.zero else Z.div x y)". *)
(* Extract Inlined Constant Z.rem => "(fun x y -> if Z.equal y Z.zero then x else Z.rem x y)". *)
(* Extract Inlined Constant Z.quotrem => "(fun x y -> if Z.equal y Z.zero then (Z.zero, x) else Z.div_rem x y)". *)
(** * Booleans. Without these, [negb]/[andb]/[orb] stay Rocq definitions
    rather than OCaml's native ones. The laziness of [&&]/[||] is
    unobservable here: extracted code is pure and total. *)
Extract Inlined Constant negb => "not".
Extract Inlined Constant andb => "(&&)".
(* Extract Inlined Constant orb => "(||)". *)
(* Extract Inlined Constant xorb => "(<>)". *)


(** * Pairs and other data types *)
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
