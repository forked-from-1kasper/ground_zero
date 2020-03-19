import ground_zero.types.equiv

namespace ground_zero.types
hott theory

universes u v w

namespace sigma
  variables {α : Type u} {β : α → Type v}

  abbreviation pr₁ (x : Σ (x : α), β x) := x.fst
  abbreviation pr₂ (x : Σ (x : α), β x) := x.snd

  def elim {γ : Type w} (g : Π (x : α), β x → γ) : sigma β → γ
  | ⟨a, b⟩ := g a b

  def ind {π : sigma β → Type w} (g : Π (a : α) (b : β a), π ⟨a, b⟩) :
    Π (x : sigma β), π x
  | ⟨a, b⟩ := g a b

  def prod {α : Type u} {β : α → Type v} {u v : sigma β}
    (h : u.fst = v.fst) (g : equiv.subst h u.snd = v.snd) : u = v := begin
    cases u with x u, cases v with y v,
    fapply equiv.transport (λ (v : β y), ⟨x, u⟩ = ⟨y, v⟩ :> sigma β),
    exact g,
    apply @eq.rec α x (λ (y : α) (h : x = y),
      ⟨x, u⟩ = ⟨y, equiv.subst h u⟩ :> sigma β),
    trivial
  end

  def prod_refl {α : Type u} {β : α → Type v} (u : sigma β) :
    prod eq.rfl eq.rfl = eq.refl u :=
  begin cases u with x u, trivial end
end sigma

end ground_zero.types