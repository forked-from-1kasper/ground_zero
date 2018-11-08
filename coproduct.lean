import ground_zero.equiv

namespace ground_zero

universes u v f

inductive coproduct (α : Type u) (β : Type v)
| inl {} : α → coproduct
| inr {} : β → coproduct
infix ` + ` := coproduct

namespace coproduct
  variables {α : Type u} {β : Type v}

  def elim {γ : Type f} (g₀ : α → γ) (g₁ : β → γ) : α + β → γ
  | (inl a) := g₀ a
  | (inr b) := g₁ b

  def inv : α + β → β + α
  | (coproduct.inl x) := coproduct.inr x
  | (coproduct.inr x) := coproduct.inl x

  theorem symm : α + β ≃ β + α := begin
    existsi inv, split; existsi inv;
    { intro x; induction x; trivial }
  end
end coproduct

end ground_zero