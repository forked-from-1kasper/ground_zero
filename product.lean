import ground_zero.equiv ground_zero.interval

namespace ground_zero

universes u v t

namespace product
  variables {α : Sort u} {β : Sort v}

  def elim {γ : Sort t} (g : α → β → γ) (x : α × β) : γ :=
  g x.pr₁ x.pr₂

  def uniq : Π (x : α × β), (intro x.pr₁ x.pr₂) = x :> (α × β)
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
    { simp [equiv.homotopy], intro f, apply interval.funext,
      simp [e₁, e₂], intro x, simp, apply product.uniq },
    { simp [equiv.homotopy], intro x,
      cases x with f g, simp }
  end

  def swap : α × β → β × α
  | (intro a b) := intro b a

  theorem comm : α × β ≃ β × α := begin
    existsi swap, split; existsi swap,
    repeat { intro x, induction x with a b, simp [swap] }
  end
end product

end ground_zero