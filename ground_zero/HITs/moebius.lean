import ground_zero.cubical
open ground_zero.HITs.interval (i₀ i₁ seg)

namespace ground_zero
open ground_zero.HITs

inductive moebius.rel : 𝕀 × 𝕀 → 𝕀 × 𝕀 → Prop
| edges (x : 𝕀) : moebius.rel ⟨x, i₀⟩ ⟨−x, i₁⟩

def moebius := quot moebius.rel

namespace moebius
  def elem (x y : 𝕀) : moebius :=
  quot.mk rel ⟨x, y⟩

  def a : moebius := elem i₀ i₀
  def b : moebius := elem i₁ i₀
  def c : moebius := elem i₀ i₁
  def d : moebius := elem i₁ i₁

  def up : a ⇝ b :=
  <i> elem (path.seg_path # i) i₀

  def down : d ⇝ c :=
  <i> elem (path.seg_path # −i) i₁

  def edges (x : 𝕀) : (elem x i₀) ⇝ (elem (−x) i₁) :=
  path.from_equality (support.inclusion (quot.sound $ moebius.rel.edges x))
end moebius

end ground_zero