import ground_zero.equiv

namespace ground_zero

universes u v t

namespace product
  variables {α : Sort u} {β : Sort v}

  def elim {γ : Sort t} (g : α → β → γ) (x : α × β) : γ :=
  g x.pr₁ x.pr₂

  def uniq : Π (x : α × β), (intro x.pr₁ x.pr₂) = x 
  | (intro a b) := eq.refl (intro a b)

  def ind {π : α × β → Type t} (g : Π (x : α) (y : β), π (intro x y)) :
    Π (x : α × β), π x
  | (intro a b) := g a b

  def univ {ν : Type t} : (ν → α × β) ≃ (ν → α) × (ν → β) := begin
    let e₁ : (ν → α × β) → (ν → α) × (ν → β) :=
    λ f, intro (pr₁ ∘ f) (pr₂ ∘ f),
    let e₂ : (ν → α) × (ν → β) → (ν → α × β) :=
    λ f x, intro (f.pr₁ x) (f.pr₂ x),
    existsi e₁, split; existsi e₂,
    { simp [equiv.homotopy], intro f, funext,
      simp [e₁, e₂], simp, apply product.uniq },
    { simp [equiv.homotopy], intro x,
      cases x with f g, simp }
  end
end product

end ground_zero