open Quadrivalent

module Boolean_Forward =
 struct
  (** val andb : quadrivalent -> quadrivalent -> quadrivalent **)

  let andb x y =
    match x with
    | QBottom -> QBottom
    | QTrue -> (match y with
                | QBottom -> QBottom
                | QFalse -> QFalse
                | _ -> y)
    | QFalse -> (match y with
                 | QBottom -> QBottom
                 | _ -> QFalse)
    | QTop -> (match y with
               | QTrue -> x
               | x0 -> x0)

  (** val orb : quadrivalent -> quadrivalent -> quadrivalent **)

  let orb x y =
    match x with
    | QBottom -> QBottom
    | QTrue -> (match y with
                | QBottom -> QBottom
                | _ -> QTrue)
    | QFalse -> (match y with
                 | QBottom -> QBottom
                 | QTrue -> QTrue
                 | _ -> y)
    | QTop -> (match y with
               | QFalse -> x
               | x0 -> x0)

  (** val negb : quadrivalent -> quadrivalent **)

  let negb = function
  | QTrue -> QFalse
  | QFalse -> QTrue
  | x0 -> x0

  (** val xorb : quadrivalent -> quadrivalent -> quadrivalent **)

  let xorb x y =
    match x with
    | QBottom -> QBottom
    | QTrue ->
      (match y with
       | QBottom -> QBottom
       | QFalse -> x
       | _ -> (match y with
               | QTrue -> QFalse
               | QFalse -> QTrue
               | x0 -> x0))
    | QFalse -> (match y with
                 | QBottom -> QBottom
                 | _ -> y)
    | QTop ->
      (match y with
       | QTrue -> (match x with
                   | QTrue -> QFalse
                   | QFalse -> QTrue
                   | x0 -> x0)
       | QFalse -> x
       | x0 -> x0)
 end

module Boolean_Backward =
 struct
  (** val negb : quadrivalent -> quadrivalent -> quadrivalent option **)

  let negb a1 a0 =
    match a1 with
    | QBottom -> None
    | QTrue ->
      (match a0 with
       | QBottom -> Some QBottom
       | QTrue -> Some QBottom
       | _ -> None)
    | QFalse ->
      (match a0 with
       | QBottom -> Some QBottom
       | QFalse -> Some QBottom
       | _ -> None)
    | QTop ->
      (match a0 with
       | QTop -> None
       | _ -> Some (match a0 with
                    | QTrue -> QFalse
                    | QFalse -> QTrue
                    | x -> x))

  (** val andb :
      quadrivalent -> quadrivalent -> quadrivalent -> quadrivalent
      option * quadrivalent option **)

  let andb a2 a1 a0 =
    match a2 with
    | QBottom -> (None, (if equiv a1 QBottom then None else Some QBottom))
    | QTrue ->
      (match a1 with
       | QBottom -> ((Some QBottom), None)
       | QTrue ->
         (match a0 with
          | QTrue ->
            ((if equiv a2 QTrue then None else Some QTrue),
              (if equiv a1 QTrue then None else Some QTrue))
          | QTop -> (None, None)
          | _ -> ((Some QBottom), (Some QBottom)))
       | QFalse ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue -> ((Some QBottom), (Some QBottom))
          | _ -> (None, None))
       | QTop ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue ->
            ((if equiv a2 QTrue then None else Some QTrue),
              (if equiv a1 QTrue then None else Some QTrue))
          | QFalse -> (None, (Some QFalse))
          | QTop -> (None, None)))
    | QFalse ->
      (match a1 with
       | QBottom -> ((Some QBottom), None)
       | _ ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue -> ((Some QBottom), (Some QBottom))
          | _ -> (None, None)))
    | QTop ->
      (match a1 with
       | QBottom -> ((Some QBottom), None)
       | QTrue ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue ->
            ((if equiv a2 QTrue then None else Some QTrue),
              (if equiv a1 QTrue then None else Some QTrue))
          | QFalse -> ((Some QFalse), None)
          | QTop -> (None, None))
       | QFalse ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue -> ((Some QBottom), (Some QBottom))
          | _ -> (None, None))
       | QTop ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue ->
            ((if equiv a2 QTrue then None else Some QTrue),
              (if equiv a1 QTrue then None else Some QTrue))
          | _ -> (None, None)))

  (** val orb :
      quadrivalent -> quadrivalent -> quadrivalent -> quadrivalent
      option * quadrivalent option **)

  let orb a2 a1 a0 =
    match a2 with
    | QBottom -> (None, (if equiv a1 QBottom then None else Some QBottom))
    | QTrue ->
      (match a1 with
       | QBottom -> ((Some QBottom), None)
       | _ ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QFalse -> ((Some QBottom), (Some QBottom))
          | _ -> (None, None)))
    | QFalse ->
      (match a1 with
       | QBottom -> ((Some QBottom), None)
       | QTrue ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QFalse -> ((Some QBottom), (Some QBottom))
          | _ -> (None, None))
       | QFalse ->
         (match a0 with
          | QFalse ->
            ((if equiv a2 QFalse then None else Some QFalse),
              (if equiv a1 QFalse then None else Some QFalse))
          | QTop -> (None, None)
          | _ -> ((Some QBottom), (Some QBottom)))
       | QTop ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue -> (None, (Some QTrue))
          | QFalse ->
            ((if equiv a2 QFalse then None else Some QFalse),
              (if equiv a1 QFalse then None else Some QFalse))
          | QTop -> (None, None)))
    | QTop ->
      (match a1 with
       | QBottom -> ((Some QBottom), None)
       | QTrue ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QFalse -> ((Some QBottom), (Some QBottom))
          | _ -> (None, None))
       | QFalse ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue -> ((Some QTrue), None)
          | QFalse ->
            ((if equiv a2 QFalse then None else Some QFalse),
              (if equiv a1 QFalse then None else Some QFalse))
          | QTop -> (None, None))
       | QTop ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QFalse ->
            ((if equiv a2 QFalse then None else Some QFalse),
              (if equiv a1 QFalse then None else Some QFalse))
          | _ -> (None, None)))

  (** val xorb :
      quadrivalent -> quadrivalent -> quadrivalent -> quadrivalent
      option * quadrivalent option **)

  let xorb a2 a1 a0 =
    match a2 with
    | QBottom -> (None, (if equiv a1 QBottom then None else Some QBottom))
    | QTrue ->
      (match a1 with
       | QBottom -> ((Some QBottom), None)
       | QTrue ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue -> ((Some QBottom), (Some QBottom))
          | _ -> (None, None))
       | QFalse ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QFalse -> ((Some QBottom), (Some QBottom))
          | _ -> (None, None))
       | QTop ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue -> (None, (Some QFalse))
          | QFalse -> (None, (Some QTrue))
          | QTop -> (None, None)))
    | QFalse ->
      (match a1 with
       | QBottom -> ((Some QBottom), None)
       | QTrue ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QFalse -> ((Some QBottom), (Some QBottom))
          | _ -> (None, None))
       | QFalse ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue -> ((Some QBottom), (Some QBottom))
          | _ -> (None, None))
       | QTop ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTop -> (None, None)
          | x -> (None, (Some x))))
    | QTop ->
      (match a1 with
       | QBottom -> ((Some QBottom), None)
       | QTrue ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTrue -> ((Some QFalse), None)
          | QFalse -> ((Some QTrue), None)
          | QTop -> (None, None))
       | QFalse ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | QTop -> (None, None)
          | x -> ((Some x), None))
       | QTop ->
         (match a0 with
          | QBottom -> ((Some QBottom), (Some QBottom))
          | _ -> (None, None)))
 end
