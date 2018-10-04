namespace ground_zero

universes u v f

inductive coproduct (α : Type u) (β : Type v)
| inl {} : α → coproduct
| inr {} : β → coproduct
infix `+` := coproduct

namespace coproduct
  variables {α : Type u} {β : Type v}

  def elim {γ : Type f} (g₀ : α → γ) (g₁ : β → γ) : α + β → γ
  | (inl a) := g₀ a
  | (inr b) := g₁ b
end coproduct

end ground_zero