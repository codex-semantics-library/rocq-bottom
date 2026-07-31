open AbstractionCombination

type interval = Z.t WithTop.with_top * Z.t WithTop.with_top

type nb_interval = interval

val bottom : interval

val is_included : interval -> interval -> bool

val join : interval -> interval -> interval

val meet : interval -> interval -> interval

val equiv : interval -> interval -> bool

val non_bottomb : interval -> bool

val singleton : Z.t -> interval

val is_singleton : interval -> Z.t option

type classification =
| Pos
| Neg
| Across

val classify : interval -> classification

type pos_interval = interval

type neg_interval = interval

type divisor_classification =
| DivPos of pos_interval
| DivNeg of neg_interval
| DivZero
| DivAcross

val classify_divisor : nb_interval -> divisor_classification
