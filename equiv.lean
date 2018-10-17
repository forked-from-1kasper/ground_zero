namespace ground_zero

structure {u v} product (α : Sort u) (β : Sort v) :=
intro :: (pr₁ : α) (pr₂ : β)

reserve infix ` × `
infix ` × ` := product

namespace equiv
  universes u v

  def homotopy {α : Sort u} {π : α → Sort v}
    (f g : Π (x : α), π x) :=
  Π (x : α), f x = g x
  infix ` ~ ` := homotopy

  @[refl] def homotopy.id {α : Sort u} {π : α → Sort v}
    (f : Π (x : α), π x) : f ~ f :=
  begin simp [homotopy] end

  @[symm] def homotopy.symm {α : Sort u} {π : α → Sort v}
    (f g : Π (x : α), π x) (h : f ~ g) : g ~ f := begin
    simp [homotopy] at *, intros,
    apply eq.symm, apply h
  end

  @[trans] def homotopy.trans {α : Sort u} {π : α → Sort v}
    (f g h : Π (x : α), π x) (r₁ : f ~ g) (r₂ : g ~ h) : f ~ h := begin
    simp [homotopy] at *, intros, apply eq.trans,
    apply r₁, apply r₂
  end

  def linv {α : Sort u} {β : Sort v} (f : α → β) :=
  Σ' (g : β → α), g ∘ f ~ id

  def rinv {α : Sort u} {β : Sort v} (f : α → β) :=
  Σ' (g : β → α), f ∘ g ~ id

  def biinv {α : Sort u} {β : Sort v} (f : α → β) :=
  linv f × rinv f
end equiv

def {u v} equiv (α : Sort u) (β : Sort v) :=
Σ' (f : α → β), equiv.biinv f
infix ` ≃ `:25 := equiv

namespace equiv
  universes u v

  def id (α : Type u) : α ≃ α := begin
    simp [equiv], existsi id,
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
  psigma.fst ∘ idtoeqv

  def subst {α : Type u} {π : α → Type v} {a b : α}
    (p : a = b) : π a → π b :=
  begin induction p, assume x, apply x end
end equiv

end ground_zero