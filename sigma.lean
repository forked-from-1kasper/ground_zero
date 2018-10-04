namespace ground_zero

universes u v f

namespace sigma
  variables {α : Type u} {β : α → Type v}

  abbreviation pr₁ (x : Σ (x : α), β x) := x.fst
  abbreviation pr₂ (x : Σ (x : α), β x) := x.snd

  def elim {γ : Type f} (g : Π (x : α), β x → γ) : sigma β → γ
  | ⟨a, b⟩ := g a b

  def ind {π : sigma β → Type f} (g : Π (a : α) (b : β a), π ⟨a, b⟩) : Π (x : sigma β), π x
  | ⟨a, b⟩ := g a b
end sigma


end ground_zero