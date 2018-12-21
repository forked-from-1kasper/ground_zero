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

  def a : moebius := quot.mk rel ⟨i₀, i₀⟩
  def b : moebius := quot.mk rel ⟨i₁, i₀⟩
  def c : moebius := quot.mk rel ⟨i₀, i₁⟩
  def d : moebius := quot.mk rel ⟨i₁, i₁⟩

  def up : a ⇝ b :=
  <i> quot.mk rel ⟨path.seg_path # i, i₀⟩

  def down : d ⇝ c :=
  <i> quot.mk rel ⟨path.seg_path # −i, i₁⟩
end moebius

end ground_zero