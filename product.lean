namespace ground_zero

universes u v f
inductive product (α : Type u) (β : Type v) : Type (max u v)
| intro {} : α → β → product

reserve infix ` × `
infix ` × ` := product

namespace product
  variables {α : Type u} {β : Type v}

  def elim {γ : Type f} (g : α → β → γ) : α × β → γ
  | (intro a b) := g a b

  def pr₁ : α × β → α := elim (λ a b, a)
  def pr₂ : α × β → β := elim (λ a b, b)

  def uniq : Π (x : α × β), (intro x.pr₁ x.pr₂) = x 
  | (intro a b) := eq.refl (intro a b)

  def ind {π : α × β → Type f} (g : Π (x : α) (y : β), π (intro x y)) :
    Π (x : α × β), π x
  | (intro a b) := g a b
end product

end ground_zero