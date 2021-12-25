import ground_zero.theorems.funext

hott theory

namespace ground_zero.types

universes u v u' v' w

namespace product
  variables {α : Type u} {β : Type v}

  def elim {γ : Type w} (g : α → β → γ) (x : α × β) : γ :=
  g x.pr₁ x.pr₂

  def uniq : Π (x : α × β), (x.pr₁, x.pr₂) = x :> (α × β)
  | (a, b) := idp (a, b)

  def construction (a b : α) (c d : β)
    (p : a = b :> α) (q : c = d :> β) :
    (a, c) = (b, d) :> α × β :=
  begin induction p, induction q, reflexivity end

  abbreviation prod {α : Type u} {β : Type v} {a b : α} {c d : β}
    (p : a = b :> α) (q : c = d :> β) :
    (a, c) = (b, d) :> α × β :=
  construction a b c d p q

  @[hott] def prod' {α : Type u} {β : Type v} (x y : α × β) (p : x.1 = y.1) (q : x.2 = y.2) : x = y :=
  begin induction x, induction y, apply prod; assumption end

  def ind {π : α × β → Type w} (g : Π x y, π (x, y)) :
    Π (x : α × β), π x
  | (a, b) := g a b

  @[hott] def univ {ν : Type w} : (ν → α × β) ≃ (ν → α) × (ν → β) :=
  begin
    let e₁ : (ν → α × β) → (ν → α) × (ν → β) :=
    λ f, (prod.pr₁ ∘ f, prod.pr₂ ∘ f),
    let e₂ : (ν → α) × (ν → β) → (ν → α × β) :=
    λ f x, (f.pr₁ x, f.pr₂ x),
    existsi e₁, split; existsi e₂,
    { intro f, apply ground_zero.HITs.interval.funext,
      intro x, apply product.uniq },
    { intro x, cases x with f g, trivial }
  end

  def bimap {γ : Type u'} {δ : Type v'}
    (f : α → γ) (g : β → δ) : α × β → γ × δ
  | (a, b) := (f a, g b)

  def swap : α × β → β × α
  | (a, b) := (b, a)

  @[hott] def comm : α × β ≃ β × α :=
  begin
    existsi swap, split; existsi swap;
    { intro x, induction x, trivial }
  end

  instance {α : Type u} {β : Type v}
    [has_one α] [has_one β] : has_one (α × β) :=
  ⟨(1, 1)⟩
end product

end ground_zero.types