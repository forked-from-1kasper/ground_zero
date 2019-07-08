import ground_zero.cubical ground_zero.HITs.graph ground_zero.HITs.circle

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

inductive moebius.rel : I × I → I × I → Type
| glue (x : I) : moebius.rel ⟨x, 0⟩ ⟨−x, 1⟩

def moebius := graph moebius.rel

namespace moebius
  def elem (x y : I) : moebius := graph.elem ⟨x, y⟩

  def a := elem 0 0
  def b := elem 1 0
  def c := elem 0 1
  def d := elem 1 1

  def up : a ⇝ b := <i> elem i 0
  def down : d ⇝ c := <i> elem (−i) 1

  def glue (x : I) : elem x 0 = elem (−x) 1 :> moebius :=
  graph.line (rel.glue x)
end moebius

def M : S¹ → Type := circle.rec I (to_equality twist)
def moebius' := Σ b, M b

def cylinder := S¹ × I

def C : S¹ → Type := circle.rec I ground_zero.types.eq.rfl
def cylinder' := Σ b, C b

end ground_zero.HITs