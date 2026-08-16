open AbstractionCombination
open ZInterval
open ZIntervalOps

(** val refine_itv : interval -> interval -> interval option **)

let refine_itv old new0 =
  if equiv new0 old then None else Some new0

(** val impl_backward_itv :
    (nb_interval -> nb_interval -> nb_interval -> interval) -> (nb_interval
    -> nb_interval -> nb_interval -> interval) -> nb_interval -> nb_interval
    -> nb_interval -> interval option * interval option **)

let impl_backward_itv bleft bright i2 i1 i0 =
  ((refine_itv i2 (bleft i2 i1 i0)), (refine_itv i1 (bright i2 i1 i0)))

(** val refine_by : nb_interval -> interval -> interval **)

let refine_by =
  meet

(** val itv_top : interval **)

let itv_top =
  (WithTop.Top, WithTop.Top)

(** val backward_interval_add_left :
    nb_interval -> nb_interval -> nb_interval -> interval **)

let backward_interval_add_left i2 i1 i0 =
  refine_by i2 (interval_sub i0 i1)

(** val backward_interval_add_right :
    nb_interval -> nb_interval -> nb_interval -> interval **)

let backward_interval_add_right i2 i1 i0 =
  refine_by i1 (interval_sub i0 i2)

(** val backward_interval_sub_left :
    nb_interval -> nb_interval -> nb_interval -> interval **)

let backward_interval_sub_left i2 i1 i0 =
  refine_by i2 (interval_add i0 i1)

(** val backward_interval_sub_right :
    nb_interval -> nb_interval -> nb_interval -> interval **)

let backward_interval_sub_right i2 i1 i0 =
  refine_by i1 (interval_sub i2 i0)

(** val impl_backward_interval_add :
    nb_interval -> nb_interval -> nb_interval -> interval option * interval
    option **)

let impl_backward_interval_add =
  impl_backward_itv backward_interval_add_left backward_interval_add_right

(** val impl_backward_interval_sub :
    nb_interval -> nb_interval -> nb_interval -> interval option * interval
    option **)

let impl_backward_interval_sub =
  impl_backward_itv backward_interval_sub_left backward_interval_sub_right

(** val mul_solve_is_top : interval -> interval -> bool **)

let mul_solve_is_top i2 i0 =
  (&&) (itv_gammab i2 Z.zero) (itv_gammab i0 Z.zero)

(** val backward_mul_refine :
    nb_interval -> nb_interval -> nb_interval -> interval option **)

let backward_mul_refine iR i0 iKeep =
  if mul_solve_is_top iR i0
  then None
  else refine_itv iKeep (meet iKeep (interval_quot i0 iR))

(** val impl_backward_interval_mul :
    nb_interval -> nb_interval -> nb_interval -> interval option * interval
    option **)

let impl_backward_interval_mul i2 i1 i0 =
  ((backward_mul_refine i1 i0 i2), (backward_mul_refine i2 i0 i1))

(** val quot_remainder_window_sym : interval -> interval **)

let quot_remainder_window_sym = function
| (w, w0) ->
  (match w with
   | WithTop.Top -> itv_top
   | WithTop.NotTop l ->
     (match w0 with
      | WithTop.Top -> itv_top
      | WithTop.NotTop h ->
        let m = Z.sub (Z.max (Z.abs l) (Z.abs h)) Z.one in
        ((WithTop.NotTop (Z.neg m)), (WithTop.NotTop m))))

(** val quot_remainder_window :
    interval -> interval -> interval -> interval **)

let quot_remainder_window p i1 i0 =
  let s = quot_remainder_window_sym i1 in
  if itv_gammab i0 Z.zero
  then s
  else (match classify p with
        | Pos -> ((WithTop.NotTop Z.zero), (snd s))
        | Neg -> ((fst s), (WithTop.NotTop Z.zero))
        | Across -> s)

(** val interval_quot_solve_dividend : interval -> interval -> interval **)

let interval_quot_solve_dividend i1 i0 =
  let p = interval_mul i0 i1 in interval_add p (quot_remainder_window p i1 i0)

(** val bound_succ : Z.t WithTop.with_top -> Z.t WithTop.with_top **)

let bound_succ = function
| WithTop.Top -> WithTop.Top
| WithTop.NotTop z -> WithTop.NotTop (Z.add z Z.one)

(** val bound_pred : Z.t WithTop.with_top -> Z.t WithTop.with_top **)

let bound_pred = function
| WithTop.Top -> WithTop.Top
| WithTop.NotTop z -> WithTop.NotTop (Z.sub z Z.one)

(** val quot_bound_nz :
    Z.t WithTop.with_top -> Z.t -> Z.t WithTop.with_top **)

let quot_bound_nz a z =
  quot_bound a (WithTop.NotTop z)

(** val quot_divisor_pos_qlow :
    Z.t WithTop.with_top -> Z.t WithTop.with_top -> interval **)

let quot_divisor_pos_qlow h2 = function
| WithTop.Top -> itv_top
| WithTop.NotTop z ->
  if Z.lt Z.zero z
  then (WithTop.Top, (quot_bound_nz h2 z))
  else ((bound_succ (quot_bound_nz h2 (Z.sub z Z.one))), WithTop.Top)

(** val quot_divisor_pos_qhigh :
    Z.t WithTop.with_top -> Z.t WithTop.with_top -> interval **)

let quot_divisor_pos_qhigh l2 = function
| WithTop.Top -> itv_top
| WithTop.NotTop z ->
  if Z.lt z Z.zero
  then (WithTop.Top, (quot_bound_nz l2 z))
  else ((bound_succ (quot_bound_nz l2 (Z.add z Z.one))), WithTop.Top)

(** val interval_quot_solve_divisor_pos : interval -> interval -> interval **)

let interval_quot_solve_divisor_pos i2 i0 =
  itv_strictly_positive_part
    (meet (quot_divisor_pos_qlow (snd i2) (fst i0))
      (quot_divisor_pos_qhigh (fst i2) (snd i0)))

(** val quot_divisor_neg_qhigh :
    Z.t WithTop.with_top -> Z.t WithTop.with_top -> interval **)

let quot_divisor_neg_qhigh h2 = function
| WithTop.Top -> itv_top
| WithTop.NotTop z ->
  if Z.lt z Z.zero
  then ((quot_bound_nz h2 z), WithTop.Top)
  else (WithTop.Top, (bound_pred (quot_bound_nz h2 (Z.add z Z.one))))

(** val quot_divisor_neg_qlow :
    Z.t WithTop.with_top -> Z.t WithTop.with_top -> interval **)

let quot_divisor_neg_qlow l2 = function
| WithTop.Top -> itv_top
| WithTop.NotTop z ->
  if Z.lt Z.zero z
  then ((quot_bound_nz l2 z), WithTop.Top)
  else (WithTop.Top, (bound_pred (quot_bound_nz l2 (Z.sub z Z.one))))

(** val interval_quot_solve_divisor_neg : interval -> interval -> interval **)

let interval_quot_solve_divisor_neg i2 i0 =
  itv_strictly_negative_part
    (meet (quot_divisor_neg_qhigh (snd i2) (snd i0))
      (quot_divisor_neg_qlow (fst i2) (fst i0)))

(** val interval_quot_dividend_from_divisor_half :
    interval -> interval -> interval -> interval **)

let interval_quot_dividend_from_divisor_half i2 f i0 =
  meet i2
    (if non_bottomb f then interval_quot_solve_dividend f i0 else bottom)

(** val impl_backward_interval_quot :
    nb_interval -> nb_interval -> nb_interval -> interval option * interval
    option **)

let impl_backward_interval_quot i2 i1 i0 =
  match classify i1 with
  | Pos ->
    let fp = meet i1 (interval_quot_solve_divisor_pos i2 i0) in
    ((refine_itv i2 (interval_quot_dividend_from_divisor_half i2 fp i0)),
    (refine_itv i1 fp))
  | Neg ->
    let fn = meet i1 (interval_quot_solve_divisor_neg i2 i0) in
    ((refine_itv i2 (interval_quot_dividend_from_divisor_half i2 fn i0)),
    (refine_itv i1 fn))
  | Across ->
    let fn = meet i1 (interval_quot_solve_divisor_neg i2 i0) in
    let fp = meet i1 (interval_quot_solve_divisor_pos i2 i0) in
    ((refine_itv i2
       (join_possibly_bottom
         (interval_quot_dividend_from_divisor_half i2 fn i0)
         (interval_quot_dividend_from_divisor_half i2 fp i0))),
    (refine_itv i1 (join_possibly_bottom fn fp)))
