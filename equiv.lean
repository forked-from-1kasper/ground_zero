namespace ground_zero

namespace equiv
  universes u v

  def homotopy {α : Type u} {π : α → Type v}
    (f g : Π (x : α), π x) :=
  Π (x : α), f x = g x
  infix `~` := homotopy

  def linv {α β : Type u} (f : α → β) :=
  Σ' (g : β → α), g ∘ f ~ id

  def rinv {α β : Type u} (f : α → β) :=
  Σ' (g : β → α), f ∘ g ~ id

  def biinv {α β : Type u} (f : α → β) :=
  linv f × rinv f
end equiv

def {u} equiv (α β : Type u) :=
Σ (f : α → β), equiv.biinv f
infix `≃`:25 := equiv

namespace equiv
  universes u v

  def id (α : Type u) : α ≃ α := begin
    simp [equiv], apply (sigma.mk id),
    simp [biinv], simp [equiv.linv, equiv.rinv],
    split,
    repeat {
      existsi id,
      simp [homotopy]
    }
  end

  def idtoeqv {α β : Type u} (p : α = β) : α ≃ β :=
  begin induction p, apply id end

  def transport {α β : Type u} : (α = β) → (α → β) :=
  sigma.fst ∘ idtoeqv

  def subst {α : Type u} {π : α → Type v} {a b : α}
    (p : a = b) : π a → π b :=
  begin induction p, assume x, apply x end
end equiv

end ground_zero