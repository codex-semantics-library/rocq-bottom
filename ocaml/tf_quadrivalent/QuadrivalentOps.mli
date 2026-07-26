open Quadrivalent

module Boolean_Forward :
 sig
  val andb : quadrivalent -> quadrivalent -> quadrivalent

  val orb : quadrivalent -> quadrivalent -> quadrivalent

  val negb : quadrivalent -> quadrivalent

  val xorb : quadrivalent -> quadrivalent -> quadrivalent
 end

module Boolean_Backward :
 sig
  val negb : quadrivalent -> quadrivalent -> quadrivalent option

  val andb :
    quadrivalent -> quadrivalent -> quadrivalent -> quadrivalent
    option * quadrivalent option

  val orb :
    quadrivalent -> quadrivalent -> quadrivalent -> quadrivalent
    option * quadrivalent option

  val xorb :
    quadrivalent -> quadrivalent -> quadrivalent -> quadrivalent
    option * quadrivalent option
 end
