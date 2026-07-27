
module WithTop :
 sig
  type 'a with_top =
  | Top
  | NotTop of 'a

  val lift2 :
    ('a1 -> 'a2 -> 'a3) -> 'a1 with_top -> 'a2 with_top -> 'a3 with_top
 end
