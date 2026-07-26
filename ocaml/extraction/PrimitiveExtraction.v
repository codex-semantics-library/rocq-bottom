(** PrimitiveExtraction.v - How Rocq's primitive number types map to OCaml. *)


(** * Booleans

    [negb]/[andb]/[orb] are ordinary Rocq definitions, so without these they do
    not use Ocaml's native boolean. OCaml's [&&]/[||] are lazy where Rocq's are
    strict, which is unobservable here: extracted code is pure and total. *)
Extract Inlined Constant negb => "not".
Extract Inlined Constant andb => "(&&)".
Extract Inlined Constant orb => "(||)".
Extract Inlined Constant xorb => "(<>)".


(** * Pairs and other data types *)
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
