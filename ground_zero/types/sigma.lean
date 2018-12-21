namespace ground_zero.types

universes u v w

namespace sigma
  variables {α : Type u} {β : α → Type v}

  abbreviation pr₁ (x : Σ' (x : α), β x) := x.fst
  abbreviation pr₂ (x : Σ' (x : α), β x) := x.snd

  def elim {γ : Type w} (g : Π (x : α), β x → γ) : psigma β → γ
  | ⟨a, b⟩ := g a b

  def ind {π : psigma β → Type w} (g : Π (a : α) (b : β a), π ⟨a, b⟩) :
    Π (x : psigma β), π x
  | ⟨a, b⟩ := g a b
end sigma

end ground_zero.types