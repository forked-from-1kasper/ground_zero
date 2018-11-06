import ground_zero.eq

namespace ground_zero

structure {u v} product (α : Sort u) (β : Sort v) :=
intro :: (pr₁ : α) (pr₂ : β)

reserve infix ` × `
infix ` × ` := product

namespace equiv
  universes u v

  def homotopy {α : Sort u} {π : α → Sort v}
    (f g : Π (x : α), π x) :=
  Π (x : α), f x = g x :> π x
  infix ` ~ ` := homotopy

  @[refl] def homotopy.id {α : Sort u} {π : α → Sort v}
    (f : Π (x : α), π x) : f ~ f :=
  begin simp [homotopy], intro x, reflexivity end

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

  def f {α : Sort u} {β : Sort v} (e : α ≃ β) : α → β :=
  e.fst

  def g₁ {α : Sort u} {β : Sort v} (e : α ≃ β) : β → α :=
  e.snd.pr₁.fst

  def g₂ {α : Sort u} {β : Sort v} (e : α ≃ β) : β → α :=
  e.snd.pr₂.fst

  def inv₁ {α : Sort u} {β : Sort v} (e : α ≃ β) :
    e.g₁ ∘ e.f ~ id :=
  e.snd.pr₁.snd

  def inv₂ {α : Sort u} {β : Sort v} (e : α ≃ β) :
    e.f ∘ e.g₂ ~ id :=
  e.snd.pr₂.snd

  @[refl] def id (α : Sort u) : α ≃ α := begin
    simp [equiv], existsi id,
    simp [biinv], simp [equiv.linv, equiv.rinv],
    split,
    repeat {
      existsi id, simp [homotopy],
      intro, reflexivity
    }
  end

  def idtoeqv {α β : Sort u} (p : α = β :> _) : α ≃ β :=
  begin induction p, apply id end

  def transport {α β : Sort u} : (α = β :> _) → (α → β) :=
  psigma.fst ∘ idtoeqv

  def subst {α : Sort u} {π : α → Sort v} {a b : α}
    (p : a = b :> α) : π a → π b :=
  begin induction p, assume x, apply x end

  reserve infix ` ▸ `
  infix ` ▸ ` := subst
end equiv

def {u v} qinv {α : Sort u} {β : Sort v} (f : α → β) :=
Σ' (g : β → α), (f ∘ g ~ id) × (g ∘ f ~ id)

namespace qinv
  universes u v

  def equiv (α : Sort u) (β : Sort v) :=
  Σ' (f : α → β), qinv f

  def q2b {α : Sort u} {β : Sort v} (f : α → β) (q : qinv f) :
    equiv.biinv f := begin
    cases q with g H,
    cases H with α β,
    split; existsi g,
    exact β, exact α
  end

  def b2q {α : Sort u} {β : Sort v} (f : α → β) (b : equiv.biinv f) :
    qinv f := begin
    cases b with linv rinv,
    cases rinv with g α,
    cases linv with h β,

    existsi g, split,
    exact α, intro x,

    have γ₁ := β (g (f x)), simp at γ₁,
    have γ₂ := h # (α (f x)), simp at γ₂,
    exact γ₁⁻¹ ⬝ γ₂ ⬝ β x
  end
end qinv

end ground_zero