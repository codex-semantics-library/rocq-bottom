
module WithTop =
 struct
  type 'a with_top =
  | Top
  | NotTop of 'a

  (** val lift2 :
      ('a1 -> 'a2 -> 'a3) -> 'a1 with_top -> 'a2 with_top -> 'a3 with_top **)

  let lift2 f a b =
    match a with
    | Top -> Top
    | NotTop a0 -> (match b with
                    | Top -> Top
                    | NotTop b0 -> NotTop (f a0 b0))
 end
