open ZInterval

type concr = Z.t

type non_empty = nb_interval

type possibly_empty = interval

(** val singleton : concr -> non_empty **)

let singleton =
  singleton

(** val is_included : non_empty -> non_empty -> bool **)

let is_included =
  is_included

(** val embed : non_empty -> possibly_empty **)

let embed x =
  x

(** val is_non_empty : possibly_empty -> bool **)

let is_non_empty =
  non_bottomb

(** val refine : possibly_empty -> non_empty option **)

let refine x =
  if non_bottomb x then Some x else None

(** val equiv : non_empty -> non_empty -> bool **)

let equiv =
  equiv

(** val join : non_empty -> non_empty -> non_empty **)

let join =
  join

(** val meet : non_empty -> non_empty -> possibly_empty **)

let meet =
  meet
