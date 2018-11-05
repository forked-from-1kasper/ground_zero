import ground_zero.trunc ground_zero.eq ground_zero.structures
import ground_zero.equiv
open ground_zero.trunc ground_zero.structures

namespace ground_zero

def 𝕀 := ∥bool∥
abbreviation interval := 𝕀

namespace interval
  universes u v

  def i₀ : 𝕀 := trunc.elem ff
  def i₁ : 𝕀 := trunc.elem tt
  def seg : i₀ = i₁ :> 𝕀 := trunc.uniq i₀ i₁

  abbreviation zero := i₀
  abbreviation one := i₁

  @[inline, recursor 4]
  def rec {β : Sort u} (b₀ : β) (b₁ : β)
    (s : b₀ = b₁ :> β) : 𝕀 → β :=
  let f (b : bool) : singl b₀ :=
    bool.rec (singl.trivial_loop b₀) ⟨b₁, s⟩ b in
  singl.point ∘ trunc.rec f

  def hrec {β : 𝕀 → Sort u}
    (b₀ : β i₀) (b₁ : β i₁) (s : b₀ == b₁)
    (x : 𝕀) : β x :=
  @quot.hrec_on bool (λ _ _, true) β x
    (λ i, bool.rec_on i b₀ b₁)
    (λ a b _,
      begin simp, induction a; induction b; simp,
            apply s, symmetry, apply s end)

  def ind {β : 𝕀 → Prop} (b₀ : β i₀) (b₁ : β i₁) :
    Π (x : 𝕀), β x := begin
    intros, apply trunc.ind, intros,
    induction a, apply b₀, apply b₁
  end

  def homotopy {α : Sort u} {β : Sort v} {f g : α → β}
    (p : f ~ g) (x : α) : 𝕀 → β :=
  rec (f x) (g x) (p x)

  def funext {α : Sort u} {β : Sort v} {f g : α → β}
    (p : f ~ g) : f = g :> (α → β) :=
  function.swap (homotopy p) # seg

  instance : prop 𝕀 := ⟨trunc.uniq⟩
  instance trunc_functions {α : Type u} : prop (∥α∥ → ∥α∥) :=
  ⟨begin intros, apply funext, intro x, apply trunc.uniq end⟩

  def neg : 𝕀 → 𝕀 :=
  trunc.rec (trunc.elem ∘ bnot)
  prefix `−`:20 := neg

  def bool_to_interval (f : bool → bool → bool) (a b : 𝕀) : 𝕀 :=
  trunc.rec (λ a, trunc.rec (trunc.elem ∘ f a) b) a

  def min : 𝕀 → 𝕀 → 𝕀 := bool_to_interval band
  def max : 𝕀 → 𝕀 → 𝕀 := bool_to_interval bor

  notation r `∧` s := min r s
  notation r `∨` s := max r s
end interval

end ground_zero