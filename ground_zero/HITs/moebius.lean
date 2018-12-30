import ground_zero.cubical.path
open ground_zero.HITs.interval (i₀ i₁ seg)

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

namespace ground_zero
open ground_zero.HITs

inductive moebius.rel : I × I → I × I → Prop
| edges (x : I) : moebius.rel ⟨x, i₀⟩ ⟨−x, i₁⟩

def moebius := quot moebius.rel

namespace moebius
  def elem (x y : I) : moebius :=
  quot.mk rel ⟨x, y⟩

  def a : moebius := elem i₀ i₀
  def b : moebius := elem i₁ i₀
  def c : moebius := elem i₀ i₁
  def d : moebius := elem i₁ i₁

  def up : a ⇝ b :=
  <i> elem i i₀

  def down : d ⇝ c :=
  <i> elem (−i) i₁

  def edges (x : I) : (elem x i₀) ⇝ (elem (−x) i₁) :=
  cubical.cubes.from_equality
    (support.inclusion (quot.sound $ rel.edges x))
end moebius

end ground_zero