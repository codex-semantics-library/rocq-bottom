open AbstractionCombination

type interval = Z.t WithTop.with_top * Z.t WithTop.with_top

type nb_interval = interval

(** val bottom : interval **)

let bottom =
  ((WithTop.NotTop Z.one), (WithTop.NotTop Z.zero))

(** val is_included : interval -> interval -> bool **)

let is_included a2 a1 =
  let (l2, h2) = a2 in
  let (l1, h1) = a1 in
  (&&)
    (match l1 with
     | WithTop.Top -> true
     | WithTop.NotTop a3 ->
       (match l2 with
        | WithTop.Top -> false
        | WithTop.NotTop a4 -> Z.leq a3 a4))
    (match h1 with
     | WithTop.Top -> true
     | WithTop.NotTop a3 ->
       (match h2 with
        | WithTop.Top -> false
        | WithTop.NotTop a4 -> Z.leq a4 a3))

(** val join : interval -> interval -> interval **)

let join i1 i2 =
  let (l1, h1) = i1 in
  let (l2, h2) = i2 in
  ((match l1 with
    | WithTop.Top -> WithTop.Top
    | WithTop.NotTop x ->
      (match l2 with
       | WithTop.Top -> WithTop.Top
       | WithTop.NotTop y -> WithTop.NotTop (Z.min x y))),
  (match h1 with
   | WithTop.Top -> WithTop.Top
   | WithTop.NotTop x ->
     (match h2 with
      | WithTop.Top -> WithTop.Top
      | WithTop.NotTop y -> WithTop.NotTop (Z.max x y))))

(** val meet : interval -> interval -> interval **)

let meet i1 i2 =
  let (l1, h1) = i1 in
  let (l2, h2) = i2 in
  ((match l1 with
    | WithTop.Top -> l2
    | WithTop.NotTop x ->
      (match l2 with
       | WithTop.Top -> l1
       | WithTop.NotTop y -> WithTop.NotTop (Z.max x y))),
  (match h1 with
   | WithTop.Top -> h2
   | WithTop.NotTop x ->
     (match h2 with
      | WithTop.Top -> h1
      | WithTop.NotTop y -> WithTop.NotTop (Z.min x y))))

(** val equiv : interval -> interval -> bool **)

let equiv i1 i2 =
  let (l1, h1) = i1 in
  let (l2, h2) = i2 in
  (&&)
    (match l1 with
     | WithTop.Top ->
       (match l2 with
        | WithTop.Top -> true
        | WithTop.NotTop _ -> false)
     | WithTop.NotTop x ->
       (match l2 with
        | WithTop.Top -> false
        | WithTop.NotTop y -> Z.equal x y))
    (match h1 with
     | WithTop.Top ->
       (match h2 with
        | WithTop.Top -> true
        | WithTop.NotTop _ -> false)
     | WithTop.NotTop x ->
       (match h2 with
        | WithTop.Top -> false
        | WithTop.NotTop y -> Z.equal x y))

(** val non_bottomb : interval -> bool **)

let non_bottomb = function
| (w, w0) ->
  (match w with
   | WithTop.Top -> true
   | WithTop.NotTop l ->
     (match w0 with
      | WithTop.Top -> true
      | WithTop.NotTop h -> Z.leq l h))

(** val singleton : Z.t -> interval **)

let singleton k =
  ((WithTop.NotTop k), (WithTop.NotTop k))

(** val is_singleton : interval -> Z.t option **)

let is_singleton = function
| (w, w0) ->
  (match w with
   | WithTop.Top -> None
   | WithTop.NotTop l' ->
     (match w0 with
      | WithTop.Top -> None
      | WithTop.NotTop h' -> if Z.equal l' h' then Some l' else None))

type classification =
| Pos
| Neg
| Across

(** val classify : interval -> classification **)

let classify = function
| (l, h) ->
  (match l with
   | WithTop.Top ->
     (match h with
      | WithTop.Top -> Across
      | WithTop.NotTop z -> if Z.leq z Z.zero then Neg else Across)
   | WithTop.NotTop z ->
     if Z.geq z Z.zero
     then Pos
     else (match h with
           | WithTop.Top -> Across
           | WithTop.NotTop z' -> if Z.leq z' Z.zero then Neg else Across))

type pos_interval = interval

type neg_interval = interval

type across_interval = interval

type divisor_classification =
| DivPos of pos_interval
| DivNeg of neg_interval
| DivZero
| DivAcross

(** val classify_divisor : nb_interval -> divisor_classification **)

let classify_divisor = function
| (w, h) ->
  (match w with
   | WithTop.Top ->
     (match h with
      | WithTop.Top -> DivAcross
      | WithTop.NotTop h' ->
        let filtered_var = Z.lt h' Z.zero in
        if filtered_var
        then DivNeg (WithTop.Top, (WithTop.NotTop h'))
        else let filtered_var0 = Z.equal h' Z.zero in
             if filtered_var0
             then DivNeg (WithTop.Top, (WithTop.NotTop (Z.neg Z.one)))
             else DivAcross)
   | WithTop.NotTop l' ->
     let filtered_var = Z.lt Z.zero l' in
     if filtered_var
     then DivPos ((WithTop.NotTop l'), h)
     else (match h with
           | WithTop.Top ->
             let filtered_var0 = Z.equal l' Z.zero in
             if filtered_var0
             then DivPos ((WithTop.NotTop Z.one), WithTop.Top)
             else DivAcross
           | WithTop.NotTop h' ->
             let filtered_var0 = Z.lt h' Z.zero in
             if filtered_var0
             then DivNeg ((WithTop.NotTop l'), (WithTop.NotTop h'))
             else let filtered_var1 = Z.equal l' Z.zero in
                  if filtered_var1
                  then let filtered_var2 = Z.equal h' Z.zero in
                       if filtered_var2
                       then DivZero
                       else DivPos ((WithTop.NotTop Z.one), (WithTop.NotTop
                              h'))
                  else let filtered_var2 = Z.equal h' Z.zero in
                       if filtered_var2
                       then DivNeg ((WithTop.NotTop l'), (WithTop.NotTop
                              (Z.neg Z.one)))
                       else DivAcross))
