(* parse_time.ml - Parse `rocq compile -time` output from a single-threaded
   dune build and print per-file compile times, sorted descending, with the
   slow statements (>1s) listed under each slow file (>1s), annotated with
   the enclosing lemma/theorem name.

   Dune's `--display=short` emits a `coqc <path>.{glob,vo}` line before each
   file's timing output, so file attribution is direct — no text matching
   needed. The `-time` flag emits one line per sentence:

       Chars LO - HI [SNIPPET] S.SSS secs (U.Uu,U.Us)

   with *cumulative* char offsets across the whole dune run (not per-file),
   which is why we rely on the `coqc` lines rather than char positions for
   file attribution. For slow statements, the enclosing declaration name is
   found by locating the snippet in the matched file (whitespace-
   insensitively, since -time reformats spacing) and searching backwards for
   the nearest Lemma/Theorem/Example/Definition header.

   Usage: parse_time [build_dir] < dune_build_output *)

(* ---------- configuration ---------- *)

let file_threshold = 1.0
let stmt_threshold = 1.0

(* ---------- argument ---------- *)

let root =
  let d = if Array.length Sys.argv > 1 then Sys.argv.(1) else "." in
  if Filename.is_relative d then Filename.concat (Sys.getcwd ()) d else d

let relpath f =
  let prefix = root ^ "/" in
  if String.length f > String.length prefix
     && String.sub f 0 (String.length prefix) = prefix
  then String.sub f (String.length prefix) (String.length f - String.length prefix)
  else f

(* ---------- data types ---------- *)

type stmt = { txt : string; secs : float }

type file_total = {
  time : float;
  stmts : int;
  name : string;        (* relative path, for display *)
  path : string;        (* full path, for lemma lookup *)
  block : stmt array;
}

(* ---------- collect .v files into a hashtable: path -> content ---------- *)

let vfiles =
  let rec walk dir acc =
    Array.fold_left (fun acc name ->
      let path = Filename.concat dir name in
      if Sys.is_directory path then
        if name <> "_build" && name <> ".git" then walk path acc
        else acc
      else if Filename.check_suffix name ".v" && name <> "test2.v" then
        path :: acc
      else acc
    ) acc (Sys.readdir dir)
  in
  walk root []

(* [file_contents]: file path -> file content. *)
let file_contents =
  let h = Hashtbl.create (List.length vfiles) in
  List.iter (fun f ->
    let ic = open_in f in
    let len = in_channel_length ic in
    let s = really_input_string ic len in
    close_in ic;
    Hashtbl.add h f s
  ) vfiles;
  h

(* ---------- read stdin ---------- *)

let read_all ic =
  let buf = Buffer.create 65536 in
  let chunk = Bytes.create 4096 in
  let rec loop () =
    let n = input ic chunk 0 4096 in
    if n = 0 then Buffer.contents buf
    else (Buffer.add_subbytes buf chunk 0 n; loop ())
  in
  loop ()

let log = read_all stdin

(* ---------- split on \r and \n (dune progress uses \r) ---------- *)

let split_lines s =
  let rec loop i acc =
    if i >= String.length s then List.rev acc
    else begin
      let j =
        try
          let n = String.index_from s i '\n' in
          let r = try String.index_from s i '\r' with Not_found -> n in
          min n r
        with Not_found ->
          (try String.index_from s i '\r' with Not_found -> String.length s)
      in
      loop (j + 1) (String.sub s i (j - i) :: acc)
    end
  in
  loop 0 []

let lines = split_lines log

(* ---------- parse "Chars LO - HI [SNIPPET] S.SSS secs ..." ---------- *)

(* The snippet may contain ] (e.g. [Cases~[c1;~c2]~=>~...]), so we use a
   greedy .* and anchor on "] <float> secs". *)
let re_chars =
  Str.regexp "Chars \\([0-9]+\\) - \\([0-9]+\\) \\[\\(.*\\)\\] \\([0-9.]+\\) secs"

let parse_chars ln =
  if Str.string_match re_chars ln 0 then
    Some { txt = Str.matched_group 3 ln;
           secs = float_of_string (Str.matched_group 4 ln) }
  else None

(* ---------- parse "coqc <path>.{glob,vo}" lines ---------- *)

(* Dune --display=short emits these to name each file being compiled.
   The path is relative to the repo root, e.g. base.{glob,vo} or
   Transfer_function/ZInterval/MulTheory.{glob,vo}. *)
let re_coqc = Str.regexp "coqc \\([^\n\r]*\\)\\.{glob,vo}"

let parse_coqc ln =
  try
    let _ = Str.search_forward re_coqc ln 0 in
    let path = Str.matched_group 1 ln in
    let path = String.trim path in
    Some (Filename.concat root (path ^ ".v"))
  with Not_found -> None

(* ---------- split into per-file blocks at coqc lines ---------- *)

(* Each block is (file_path, statements). The file_path comes from the
   `coqc` line; the statements are the `Chars` lines that follow until the
   next `coqc` line. *)

let blocks =
  let cur_path = ref None in
  let cur_stmts = ref [] in
  let acc = ref [] in
  let flush () =
    match !cur_path with
    | None -> ()
    | Some p ->
      acc := (p, List.rev !cur_stmts) :: !acc;
      cur_path := None;
      cur_stmts := []
  in
  List.iter (fun ln ->
    (* Try coqc first — a line might contain both Done: and coqc after
       \r-splitting, but coqc lines don't start with "Chars ". *)
    (match parse_coqc ln with
     | Some p ->
       flush ();
       cur_path := Some p
     | None ->
       (match parse_chars ln with
        | Some s -> cur_stmts := s :: !cur_stmts
        | None -> ()))
  ) lines;
  flush ();
  List.rev !acc

(* ---------- text helpers ---------- *)

(* Replace ~ with space (rocq -time uses ~ for spaces in snippets). *)
let norm s = Str.global_replace (Str.regexp "~") " " s

(* Strip the trailing "..." that rocq -time appends to truncated snippets. *)
let strip_dots s =
  let len = String.length s in
  if len >= 3 && String.sub s (len - 3) 3 = "..." then
    String.sub s 0 (len - 3)
  else s

(* Strip leading "(" that rocq -time wraps around multi-statement snippets. *)
let strip_paren s =
  if String.length s > 0 && String.get s 0 = '(' then String.sub s 1 (String.length s - 1)
  else s

let skip_prefixes = [|
  "Require"; "Import"; "Open Scope"; "From Stdlib";
  "Set "; "Declare Scope"; "Proof"; "Qed";
  "Next Obligation"; "Obligation"; "Arguments";
  "Notation"; "Infix"; "Scope"; "End "; "Module"; "Section";
  "Global "; "Local "; "#["; "Hint"; "Existing "; "Coercion"
|]

let starts_with_any s prefs =
  Array.exists (fun p ->
    String.length s >= String.length p &&
    String.sub s 0 (String.length p) = p
  ) prefs

let find_sub needle haystack =
  try
    let _ = Str.search_forward (Str.regexp_string needle) haystack 0 in
    Some (Str.match_beginning ())
  with Not_found -> None

(* ---------- enclosing declaration name ---------- *)

(* A regex matching a declaration header, capturing the name. *)
let re_decl =
  Str.regexp
    "\\(Lemma\\|Theorem\\|Example\\|Fact\\|Proposition\\|Definition\\|Fixpoint\\|CoFixpoint\\|Remark\\|Corollary\\|Let\\) \\([A-Za-z_][A-Za-z0-9_']*\\)"

(* Given a file content and a position [pos], search backwards for the
   nearest declaration header and return its name. *)
let enclosing_decl content pos =
  let prefix = String.sub content 0 pos in
  let best = ref None in
  let rec find_last start =
    try
      let _ = Str.search_forward re_decl prefix start in
      let kw_end = Str.match_end () in
      let name = Str.matched_group 2 prefix in
      best := Some name;
      find_last kw_end
    with Not_found -> ()
  in
  find_last 0;
  !best

(* ---------- whitespace-insensitive search for lemma lookup ---------- *)

(* Strip all whitespace, for matching -time snippets against source text
   despite spacing differences. Returns an approximate position in the
   *original* haystack. *)
let strip_ws s = Str.global_replace (Str.regexp "[ \t\n\r]+") "" s

let find_sub_ws needle haystack =
  let n = strip_ws needle in
  let h = strip_ws haystack in
  match find_sub n h with
  | None -> None
  | Some hpos ->
    (* Map position in stripped h back to original by counting non-ws chars. *)
    let orig = ref 0 and coll = ref 0 in
    while !coll < hpos && !orig < String.length haystack do
      let c = String.get haystack !orig in
      if c = ' ' || c = '\t' || c = '\n' || c = '\r' then incr orig
      else (incr orig; incr coll)
    done;
    Some !orig

(* ---------- enclosing lemma for a statement ---------- *)

(* Given the file path and a statement, find the snippet in the file content
   and return the enclosing declaration name (or "??").
   Tries progressively shorter fragments of the snippet until one matches,
   since -time truncates and reformats the tactic text. *)
let stmt_lemma path s =
  match Hashtbl.find_opt file_contents path with
  | None -> "??"
  | Some content ->
    let nt = norm s.txt |> strip_dots |> strip_paren in
    let rec try_key len =
      if len < 10 then "??"
      else begin
        let key = if String.length nt > len then String.sub nt 0 len else nt in
        (match find_sub_ws key content with
         | Some pos -> (match enclosing_decl content pos with
                        | Some name -> name
                        | None -> "??")
         | None -> try_key (len - 10))
      end
    in
    try_key 50

(* ---------- aggregate ---------- *)

let totals =
  blocks |> List.map (fun (path, stmts) ->
    let arr = Array.of_list stmts in
    let time = Array.fold_left (fun acc s -> acc +. s.secs) 0.0 arr in
    { time; stmts = Array.length arr; name = relpath path; path; block = arr })
  |> List.sort (fun a b -> compare b.time a.time)

(* ---------- print ---------- *)

let preview s =
  let txt = norm s.txt in
  if String.length txt > 60 then String.sub txt 0 60 ^ "…" else txt

let print_stmt path s =
  let lemma = stmt_lemma path s in
  Printf.printf "%8.2f           %s: %s\n" s.secs lemma (preview s)

let slow_stmts ft =
  ft.block |> Array.to_list
  |> List.filter (fun s ->
       s.secs >= stmt_threshold &&
       not (starts_with_any (norm s.txt) skip_prefixes))
  |> List.sort (fun a b -> compare b.secs a.secs)

let () =
  Printf.printf "%8s  %6s  %s\n" "time(s)" "stmts" "file";
  List.iter (fun ft ->
    Printf.printf "%8.2f  %6d  %s\n" ft.time ft.stmts ft.name;
    if ft.time >= file_threshold then
      List.iter (print_stmt ft.path) (slow_stmts ft)
  ) totals;
  let total = List.fold_left (fun acc ft -> acc +. ft.time) 0.0 totals in
  Printf.printf "\nTotal: %.1fs across %d files\n" total (List.length totals)