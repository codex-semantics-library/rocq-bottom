open AbstractionCombination
open Quadrivalent
open ZInterval

val neg_bound : Z.t WithTop.with_top -> Z.t WithTop.with_top

val interval_add : interval -> interval -> interval

val interval_sub : interval -> interval -> interval

val bound_mul :
  Z.t WithTop.with_top -> Z.t WithTop.with_top -> Z.t WithTop.with_top

val interval_mul : interval -> interval -> interval

val quot_bound :
  Z.t WithTop.with_top -> Z.t WithTop.with_top -> Z.t WithTop.with_top

val interval_quot : interval -> nb_interval -> interval

val may_be_true_leb : Z.t WithTop.with_top -> Z.t WithTop.with_top -> bool

val may_be_false_leb : Z.t WithTop.with_top -> Z.t WithTop.with_top -> bool

val interval_leb : interval -> interval -> quadrivalent

val may_be_true_eqb :
  Z.t WithTop.with_top -> Z.t WithTop.with_top -> Z.t WithTop.with_top -> Z.t
  WithTop.with_top -> bool

val interval_eqb : interval -> interval -> quadrivalent
