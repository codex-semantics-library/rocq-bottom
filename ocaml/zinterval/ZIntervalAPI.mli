open ZInterval

type concr = Z.t

type non_empty = nb_interval

type possibly_empty = interval

val singleton : concr -> non_empty

val is_included : non_empty -> non_empty -> bool

val embed : non_empty -> possibly_empty

val is_non_empty : possibly_empty -> bool

val refine : possibly_empty -> non_empty option

val equiv : non_empty -> non_empty -> bool

val join : non_empty -> non_empty -> non_empty

val meet : non_empty -> non_empty -> possibly_empty
