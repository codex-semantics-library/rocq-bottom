open AbstractionCombination
open Quadrivalent
open ZInterval

(** val neg_bound : Z.t WithTop.with_top -> Z.t WithTop.with_top **)

let neg_bound = function
| WithTop.Top -> WithTop.Top
| WithTop.NotTop z -> WithTop.NotTop (Z.neg z)

(** val interval_add : interval -> interval -> interval **)

let interval_add i2 i1 =
  let (l2, h2) = i2 in
  let (l1, h1) = i1 in
  ((WithTop.lift2 Z.add l2 l1), (WithTop.lift2 Z.add h2 h1))

(** val interval_sub : interval -> interval -> interval **)

let interval_sub i1 i2 =
  let (l1, h1) = i1 in
  let (l2, h2) = i2 in
  ((WithTop.lift2 Z.sub l1 h2), (WithTop.lift2 Z.sub h1 l2))

(** val bound_mul :
    Z.t WithTop.with_top -> Z.t WithTop.with_top -> Z.t WithTop.with_top **)

let bound_mul a b =
  match a with
  | WithTop.Top ->
    (match b with
     | WithTop.Top -> WithTop.Top
     | WithTop.NotTop y ->
       if Z.equal y Z.zero then WithTop.NotTop Z.zero else WithTop.Top)
  | WithTop.NotTop x ->
    if Z.equal x Z.zero
    then WithTop.NotTop Z.zero
    else (match b with
          | WithTop.Top -> WithTop.Top
          | WithTop.NotTop y ->
            if Z.equal y Z.zero
            then WithTop.NotTop Z.zero
            else WithTop.NotTop (Z.mul x y))

(** val interval_mul_opt : interval -> interval -> interval **)

let interval_mul_opt i2 i1 = match i1 with
| (l1, h1) ->
  let (l2, h2) = i2 in
  (match classify i1 with
   | Pos ->
     (match classify i2 with
      | Pos -> ((bound_mul l1 l2), (bound_mul h1 h2))
      | Neg -> ((bound_mul h1 l2), (bound_mul l1 h2))
      | Across -> ((bound_mul h1 l2), (bound_mul h1 h2)))
   | Neg ->
     (match classify i2 with
      | Pos -> ((bound_mul l1 h2), (bound_mul h1 l2))
      | Neg -> ((bound_mul h1 h2), (bound_mul l1 l2))
      | Across -> ((bound_mul l1 h2), (bound_mul l1 l2)))
   | Across ->
     (match classify i2 with
      | Pos -> ((bound_mul l1 h2), (bound_mul h1 h2))
      | Neg -> ((bound_mul h1 l2), (bound_mul l1 l2))
      | Across ->
        join ((bound_mul l1 h2), (bound_mul l1 l2)) ((bound_mul h1 l2),
          (bound_mul h1 h2))))

(** val quot_bound :
    Z.t WithTop.with_top -> Z.t WithTop.with_top -> Z.t WithTop.with_top **)

let quot_bound a = function
| WithTop.Top -> WithTop.NotTop Z.zero
| WithTop.NotTop b0 ->
  (match a with
   | WithTop.Top -> WithTop.Top
   | WithTop.NotTop a0 -> WithTop.NotTop (Z.div a0 b0))

(** val interval_quot_opt : interval -> nb_interval -> interval **)

let interval_quot_opt i2 i1 =
  let (l2, h2) = i2 in
  (match classify_divisor i1 with
   | DivPos p ->
     let (l1, h1) = p in
     let filtered_var = classify i2 in
     (match filtered_var with
      | Pos -> ((quot_bound l2 h1), (quot_bound h2 l1))
      | Neg -> ((quot_bound l2 l1), (quot_bound h2 h1))
      | Across -> ((quot_bound l2 l1), (quot_bound h2 l1)))
   | DivNeg n ->
     let (l1, h1) = n in
     let filtered_var = classify i2 in
     (match filtered_var with
      | Pos -> ((quot_bound h2 h1), (quot_bound l2 l1))
      | Neg -> ((quot_bound h2 l1), (quot_bound l2 h1))
      | Across -> ((quot_bound h2 h1), (quot_bound l2 h1)))
   | DivZero -> bottom
   | DivAcross ->
     let filtered_var = classify i2 in
     (match filtered_var with
      | Pos -> ((neg_bound h2), h2)
      | Neg -> (l2, (neg_bound l2))
      | Across -> join (l2, (neg_bound l2)) ((neg_bound h2), h2)))

(** val may_be_true_leb :
    Z.t WithTop.with_top -> Z.t WithTop.with_top -> bool **)

let may_be_true_leb l2 h1 =
  match l2 with
  | WithTop.Top -> true
  | WithTop.NotTop l2' ->
    (match h1 with
     | WithTop.Top -> true
     | WithTop.NotTop h1' -> Z.leq l2' h1')

(** val may_be_false_leb :
    Z.t WithTop.with_top -> Z.t WithTop.with_top -> bool **)

let may_be_false_leb h2 l1 =
  match h2 with
  | WithTop.Top -> true
  | WithTop.NotTop h2' ->
    (match l1 with
     | WithTop.Top -> true
     | WithTop.NotTop l1' -> not (Z.leq h2' l1'))

(** val interval_leb : interval -> interval -> quadrivalent **)

let interval_leb i2 i1 =
  let (l2, h2) = i2 in
  let (l1, h1) = i1 in
  to_quadrivalent (may_be_true_leb l2 h1) (may_be_false_leb h2 l1)

(** val nbinterval_leb : nb_interval -> nb_interval -> quadrivalent **)

let nbinterval_leb =
  interval_leb

(** val may_be_true_eqb :
    Z.t WithTop.with_top -> Z.t WithTop.with_top -> Z.t WithTop.with_top ->
    Z.t WithTop.with_top -> bool **)

let may_be_true_eqb l1 h1 l2 h2 =
  (&&)
    (match l2 with
     | WithTop.Top -> true
     | WithTop.NotTop l2' ->
       (match h1 with
        | WithTop.Top -> true
        | WithTop.NotTop h1' -> Z.leq l2' h1'))
    (match l1 with
     | WithTop.Top -> true
     | WithTop.NotTop l1' ->
       (match h2 with
        | WithTop.Top -> true
        | WithTop.NotTop h2' -> Z.leq l1' h2'))

(** val interval_eqb_opt : interval -> interval -> quadrivalent **)

let interval_eqb_opt i2 i1 =
  let (l2, h2) = i2 in
  let (l1, h1) = i1 in
  (match is_singleton (l1, h1) with
   | Some x1 ->
     (match is_singleton (l2, h2) with
      | Some x2 -> if Z.equal x1 x2 then QTrue else QFalse
      | None -> if may_be_true_eqb l1 h1 l2 h2 then QTop else QFalse)
   | None -> if may_be_true_eqb l1 h1 l2 h2 then QTop else QFalse)
