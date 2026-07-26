
type quadrivalent =
| QBottom
| QTrue
| QFalse
| QTop

(** val singleton : bool -> quadrivalent **)

let singleton = function
| true -> QTrue
| false -> QFalse

(** val is_included : quadrivalent -> quadrivalent -> bool **)

let is_included q1 q2 =
  match q1 with
  | QBottom -> true
  | QTrue -> (match q2 with
              | QBottom -> false
              | QFalse -> false
              | _ -> true)
  | QFalse -> (match q2 with
               | QBottom -> false
               | QTrue -> false
               | _ -> true)
  | QTop -> (match q2 with
             | QTop -> true
             | _ -> false)

(** val to_quadrivalent : bool -> bool -> quadrivalent **)

let to_quadrivalent may_true may_false =
  if may_true
  then if may_false then QTop else QTrue
  else if may_false then QFalse else QBottom

(** val equiv : quadrivalent -> quadrivalent -> bool **)

let equiv q1 q2 =
  match q1 with
  | QBottom -> (match q2 with
                | QBottom -> true
                | _ -> false)
  | QTrue -> (match q2 with
              | QTrue -> true
              | _ -> false)
  | QFalse -> (match q2 with
               | QFalse -> true
               | _ -> false)
  | QTop -> (match q2 with
             | QTop -> true
             | _ -> false)

(** val join : quadrivalent -> quadrivalent -> quadrivalent **)

let join x y =
  match x with
  | QBottom -> (match y with
                | QTop -> QTop
                | _ -> y)
  | QTrue -> (match y with
              | QBottom -> x
              | QTrue -> QTrue
              | _ -> QTop)
  | QFalse -> (match y with
               | QBottom -> x
               | QTrue -> QTop
               | x0 -> x0)
  | QTop -> QTop

(** val meet : quadrivalent -> quadrivalent -> quadrivalent **)

let meet x y =
  match x with
  | QBottom -> QBottom
  | QTrue -> (match y with
              | QTrue -> QTrue
              | QTop -> x
              | _ -> QBottom)
  | QFalse -> (match y with
               | QFalse -> QFalse
               | QTop -> x
               | _ -> QBottom)
  | QTop -> (match y with
             | QBottom -> QBottom
             | _ -> y)
