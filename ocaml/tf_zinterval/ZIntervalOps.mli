open AbstractionCombination
open Quadrivalent
open ZInterval

val neg_bound : Z.t WithTop.with_top -> Z.t WithTop.with_top

val interval_add : interval -> interval -> interval

val interval_sub : interval -> interval -> interval

val bound_mul :
  Z.t WithTop.with_top -> Z.t WithTop.with_top -> Z.t WithTop.with_top

val interval_mul_opt : interval -> interval -> interval

val quot_bound :
  Z.t WithTop.with_top -> Z.t WithTop.with_top -> Z.t WithTop.with_top

val interval_quot_opt : interval -> nb_interval -> interval

val may_be_true_leb : Z.t WithTop.with_top -> Z.t WithTop.with_top -> bool

val may_be_false_leb : Z.t WithTop.with_top -> Z.t WithTop.with_top -> bool

val interval_leb : interval -> interval -> quadrivalent

val nbinterval_leb : nb_interval -> nb_interval -> quadrivalent

val may_be_true_eqb :
  Z.t WithTop.with_top -> Z.t WithTop.with_top -> Z.t WithTop.with_top -> Z.t
  WithTop.with_top -> bool

val interval_eqb_opt : interval -> interval -> quadrivalent
