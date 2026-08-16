open AbstractionCombination
open ZInterval
open ZIntervalOps

val refine_itv : interval -> interval -> interval option

val impl_backward_itv :
  (nb_interval -> nb_interval -> nb_interval -> interval) -> (nb_interval ->
  nb_interval -> nb_interval -> interval) -> nb_interval -> nb_interval ->
  nb_interval -> interval option * interval option

val refine_by : nb_interval -> interval -> interval

val itv_top : interval

val backward_interval_add_left :
  nb_interval -> nb_interval -> nb_interval -> interval

val backward_interval_add_right :
  nb_interval -> nb_interval -> nb_interval -> interval

val backward_interval_sub_left :
  nb_interval -> nb_interval -> nb_interval -> interval

val backward_interval_sub_right :
  nb_interval -> nb_interval -> nb_interval -> interval

val impl_backward_interval_add :
  nb_interval -> nb_interval -> nb_interval -> interval option * interval
  option

val impl_backward_interval_sub :
  nb_interval -> nb_interval -> nb_interval -> interval option * interval
  option

val mul_solve_is_top : interval -> interval -> bool

val backward_mul_refine :
  nb_interval -> nb_interval -> nb_interval -> interval option

val impl_backward_interval_mul :
  nb_interval -> nb_interval -> nb_interval -> interval option * interval
  option

val quot_remainder_window_sym : interval -> interval

val quot_remainder_window : interval -> interval -> interval -> interval

val interval_quot_solve_dividend : interval -> interval -> interval

val bound_succ : Z.t WithTop.with_top -> Z.t WithTop.with_top

val bound_pred : Z.t WithTop.with_top -> Z.t WithTop.with_top

val quot_bound_nz : Z.t WithTop.with_top -> Z.t -> Z.t WithTop.with_top

val quot_divisor_pos_qlow :
  Z.t WithTop.with_top -> Z.t WithTop.with_top -> interval

val quot_divisor_pos_qhigh :
  Z.t WithTop.with_top -> Z.t WithTop.with_top -> interval

val interval_quot_solve_divisor_pos : interval -> interval -> interval

val quot_divisor_neg_qhigh :
  Z.t WithTop.with_top -> Z.t WithTop.with_top -> interval

val quot_divisor_neg_qlow :
  Z.t WithTop.with_top -> Z.t WithTop.with_top -> interval

val interval_quot_solve_divisor_neg : interval -> interval -> interval

val interval_quot_dividend_from_divisor_half :
  interval -> interval -> interval -> interval

val impl_backward_interval_quot :
  nb_interval -> nb_interval -> nb_interval -> interval option * interval
  option
