import ground_zero.cubical

/-
  The Möbius band as quotient of square I × I.
  * https://en.wikipedia.org/wiki/M%C3%B6bius_strip#Topology

  -------->
  |   A   |
  |       |
  |   A   |
  <--------
  Edges labelled A are joined that
  so the directions of arrows match.
-/

namespace ground_zero.HITs
open ground_zero.cubical

inductive moebius.rel : I × I → I × I → Prop
| glue (x : I) : moebius.rel ⟨x, 0⟩ ⟨−x, 1⟩

def moebius := quot moebius.rel

namespace moebius
  def elem (x y : I) : moebius := quot.mk rel ⟨x, y⟩

  def a := elem 0 0
  def b := elem 1 0
  def c := elem 0 1
  def d := elem 1 1

  def up : a ⇝ b := <i> elem i 0
  def down : d ⇝ c := <i> elem (−i) 1

  def glue (x : I) : elem x 0 = elem (−x) 1 :> moebius :=
  ground_zero.support.inclusion (quot.sound $ rel.glue x)
end moebius

end ground_zero.HITs