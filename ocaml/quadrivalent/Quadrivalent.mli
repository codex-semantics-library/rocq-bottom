
type quadrivalent =
| QBottom
| QTrue
| QFalse
| QTop

val singleton : bool -> quadrivalent

val is_included : quadrivalent -> quadrivalent -> bool

val to_quadrivalent : bool -> bool -> quadrivalent

val equiv : quadrivalent -> quadrivalent -> bool

val join : quadrivalent -> quadrivalent -> quadrivalent

val meet : quadrivalent -> quadrivalent -> quadrivalent
