import ground_zero.trunc ground_zero.eq ground_zero.structures
open ground_zero.trunc ground_zero.structures

namespace ground_zero

def 𝕀 := ∥bool∥
namespace 𝕀
  universes u v

  def i₀ : 𝕀 := trunc.elem ff
  def i₁ : 𝕀 := trunc.elem tt
  def seg : i₀ = i₁ := trunc.uniq i₀ i₁

  @[inline, recursor 4]
  def rec {β : Sort u} (b₀ : β) (b₁ : β) (s : b₀ = b₁) : 𝕀 → β :=
  let f (b : bool) : eq.singl b₀ :=
    bool.rec (eq.trivial_loop b₀) ⟨b₁, s⟩ b in
  eq.end_point ∘ trunc.rec f

  def ind {β : 𝕀 → Prop} (b₀ : β i₀) (b₁ : β i₁) :
    Π (x : 𝕀), β x := begin
    intros, apply trunc.ind, intros,
    induction a, apply b₀, apply b₁
  end

  instance : prop 𝕀 := ⟨trunc.uniq⟩

  def neg : 𝕀 → 𝕀 :=
  trunc.rec (trunc.elem ∘ bnot)
  prefix `−`:20 := neg

  def funext {α : Sort u} {β : Sort v} {f g : α → β}
    (p : Π (x : α), f x = g x) : f = g := begin
    let pₓ := λ (x : α), rec (f x) (g x) (p x),
    let q := λ (i : 𝕀) (x : α), pₓ x i,
    apply (eq.map q seg)
  end
end 𝕀

end ground_zero