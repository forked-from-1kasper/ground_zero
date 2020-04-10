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
    (p : u.fst = v.fst) (q : equiv.subst p u.snd = v.snd) : u = v := begin
    cases u with x u, cases v with y v,
    change x = y at p, induction p,
    change u = v at q, induction q,
    reflexivity
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

  @[hott] def map {α : Type v} {η ε : α → Type u}
    (f : Π x, η x → ε x) : (Σ x, η x) → (Σ x, ε x)
  | ⟨x, p⟩ := ⟨x, f x p⟩

  @[hott] def respects_equiv {α : Type v} {η ε : α → Type u}
    (e : Π x, η x ≃ ε x) : (Σ x, η x) ≃ (Σ x, ε x) := begin
    existsi map (λ x, (e x).forward), split,
    { existsi map (λ x, (e x).left), intro x,
      induction x with x p, fapply prod,
      { trivial },
      { transitivity, apply (e x).left_forward, trivial } },
    { existsi map (λ x, (e x).right), intro x,
      induction x with x p, fapply prod,
      { trivial },
      { transitivity, apply (e x).forward_right, trivial } }
  end

  @[hott] def hmtpy_inv_eqv {α : Type v} {β : Type u} (f g : α → β) :
    (Σ x, f x = g x) ≃ (Σ x, g x = f x) := begin
    existsi hmtpy_inv f g, split; existsi hmtpy_inv g f;
    { intro x, induction x with x h,
      fapply prod, refl,
      transitivity, apply equiv.transport_over_hmtpy,
      transitivity, apply eq.refl_right,
      apply eq.inv_inv },
  end

  @[hott] def sigma_eq_of_eq {α : Type u} {β : α → Type v} {a b : Σ x, β x}
    (p : a = b) : (Σ (p : a.fst = b.fst), equiv.subst p a.snd = b.snd) :=
  begin induction p, existsi (idp a.fst), reflexivity end

  @[hott] def eq_of_sigma_eq {α : Type u} {β : α → Type v} {a b : Σ x, β x}
    (p : Σ (p : a.fst = b.fst), equiv.subst p a.snd = b.snd) : (a = b) :=
  sigma.prod p.fst p.snd

  @[hott] def sigma_path {α : Type u} {β : α → Type v} {a b : Σ x, β x} :
    (a = b) ≃ (Σ (p : a.fst = b.fst), equiv.subst p a.snd = b.snd) := begin
    existsi sigma_eq_of_eq, split; existsi eq_of_sigma_eq,
    { intro p, induction p, induction a, induction b, reflexivity },
    { intro p,
      induction a with a u,
      induction b with b v,
      induction p with p q,
      change a = b at p, induction p,
      change u = v at q, induction q,
      reflexivity }
  end
end sigma

end ground_zero.types