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

  @[hott] def prod {α : Type u} {β : α → Type v} {u v : sigma β}
    (h : u.fst = v.fst) (g : equiv.subst h u.snd = v.snd) : u = v := begin
    cases u with x u, cases v with y v,
    fapply equiv.transport (λ (v : β y), ⟨x, u⟩ = ⟨y, v⟩ :> sigma β), exact g,
    apply @eq.rec α x (λ (y : α) (h : x = y),
      ⟨x, u⟩ = ⟨y, equiv.subst h u⟩ :> sigma β),
    trivial
  end

  @[hott] def prod_refl {α : Type u} {β : α → Type v} (u : sigma β) :
    prod eq.rfl eq.rfl = eq.refl u :=
  begin cases u with x u, trivial end

  @[hott] def spec {α : Type u} {β : Type v} : (Σ (a : α), β) → α × β
  | ⟨x, y⟩ := ⟨x, y⟩
  @[hott] def gen {α : Type u} {β : Type v} : α × β → Σ (a : α), β
  | ⟨x, y⟩ := ⟨x, y⟩
  
  @[hott] def const (α : Type u) (β : Type v) :
    (Σ (a : α), β) ≃ α × β := begin
    existsi spec, split; existsi gen;
    { intro x, induction x, trivial }
  end

  @[hott] def hmtpy_inv {α : Type v} {β : Type u} (f g : α → β) :
    (Σ x, f x = g x) → (Σ x, g x = f x)
  | ⟨x, h⟩ := ⟨x, h⁻¹⟩

  @[hott] def hmtpy_inv_eqv {α : Type v} {β : Type u} (f g : α → β) :
    (Σ x, f x = g x) ≃ (Σ x, g x = f x) := begin
    existsi hmtpy_inv f g, split; existsi hmtpy_inv g f;
    { intro x, induction x with x h,
      fapply prod, refl,
      transitivity, apply equiv.transport_over_hmtpy,
      transitivity, apply eq.refl_right,
      apply eq.inv_inv },
  end
end sigma

end ground_zero.types