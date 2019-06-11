import ground_zero.types.equiv

namespace ground_zero.types
hott theory

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

  lemma prod {α : Sort u} {β : α → Sort v} {u v : psigma β}
    (h : u.fst = v.fst) (g : equiv.subst h u.snd = v.snd) : u = v := begin
    cases u with x u, cases v with y v,
    fapply equiv.transport (λ (v : β y), ⟨x, u⟩ = ⟨y, v⟩ :> psigma β),
    exact g,
    apply @eq.rec α x (λ (y : α) (h : x = y),
      ⟨x, u⟩ = ⟨y, equiv.subst h u⟩ :> psigma β),
    trivial
  end
end sigma

end ground_zero.types