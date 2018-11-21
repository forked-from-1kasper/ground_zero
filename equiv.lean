import ground_zero.support ground_zero.functions

namespace ground_zero

structure {u v} product (α : Sort u) (β : Sort v) :=
intro :: (pr₁ : α) (pr₂ : β)
attribute [pp_using_anonymous_constructor] product

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
  universes u v w

  instance forward_coe {α : Sort u} {β : Sort v} :
    has_coe (α ≃ β) (α → β) :=
  ⟨begin intro e, cases e with f H, exact f end⟩

  @[refl] def id (α : Sort u) : α ≃ α := begin
    existsi id, split,
    repeat {
      existsi id, intro, reflexivity
    }
  end

  @[trans] def trans {α : Sort u} {β : Sort v} {γ : Sort w}
    (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ := begin
    cases e₁ with f₁ H₁,
    cases H₁ with linv₁ rinv₁,
    cases linv₁ with g₁ α₁,
    cases rinv₁ with h₁ β₁,

    cases e₂ with f₂ H₂,
    cases H₂ with linv₂ rinv₂,
    cases linv₂ with g₂ α₂,
    cases rinv₂ with h₂ β₂,

    existsi (f₂ ∘ f₁), split,
    { existsi (g₁ ∘ g₂),
      intro x, simp,
      have p := α₂ (f₁ x), simp at p,
      rw [support.truncation p],
      have q := α₁ x, simp at q, exact q },
    { existsi (h₁ ∘ h₂),
      intro x, simp,
      have p := β₁ (h₂ x), simp at p,
      rw [support.truncation p],
      have q := β₂ x, simp at q, exact q }
  end

  def idtoeqv {α β : Sort u} (p : α = β :> _) : α ≃ β :=
  begin induction p, apply id end

  def transportconst {α β : Sort u} : (α = β :> _) → (α → β) :=
  psigma.fst ∘ idtoeqv

  def subst {α : Sort u} {π : α → Sort v} {a b : α}
    (p : a = b :> α) : π a → π b :=
  begin induction p, exact functions.idfun end

  notation u ` =[` p `] ` v := equiv.subst p u = v :> _

  lemma dep_path_map {α : Sort u}
    {π : α → Sort v} {δ : α → Sort w}
    {a b : α}
    {p : a = b :> α} {u : π a} {v : π b} (q : u =[p] v)
    (g : Π {x : α}, π x → δ x) :
    g u =[p] g v :=
  begin induction q, induction p, trivial end

  theorem subst_comp {α : Sort u}
    {π : α → Sort v} {a b c : α}
    (p : a = b :> α) (q : b = c :> α) (x : π a) :
    subst (p ⬝ q) x = subst q (subst p x) :> π c :=
  begin induction p, induction q, trivial end

  -- subst with explicit π
  abbreviation transport {α : Sort u}
    (π : α → Sort v) {a b : α}
    (p : a = b :> α) : π a → π b := subst p

  lemma transport_comp {α : Sort u} {β : Sort v}
    {π : β → Sort w} {x y : α}
    (f : α → β) (p : x = y :> α) (u : π (f x)) :
    @subst α (π ∘ f) x y p u =
    subst (f # p) u :>
    π (f y) :=
  begin induction p, trivial end

  lemma transport_over_family {α : Sort u}
    {x y : α} {π δ : α → Sort v}
    (f : Π (x : α), π x → δ x)
    (p : x = y :> α) (u : π x) :
    subst p (f x u) = f y (subst p u) :> δ y :=
  begin induction p, trivial end

  def apd {α : Sort u} {β : α → Sort v} {a b : α}
    (f : Π (x : α), β x) (p : a = b :> α) :
    f a =[p] f b :=
  begin induction p, reflexivity end

  def rewrite_comp {α : Sort u} {a b c : α}
    {p : a = b :> α} {q : b = c :> α} {r : a = c :> α}
    (h : r = p ⬝ q :> a = c :> α) :
    p⁻¹ ⬝ r = q :> b = c :> α := begin
    induction p, induction q,
    simp [eq.symm], simp [eq.trans],
    simp [eq.trans] at h, exact h
  end

  reserve infix ` ▸ `
  infix [parsing_only] ` ▸ ` := subst
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

namespace equiv
  universes u v

  @[symm] def symm {α : Sort u} {β : Sort v}
    (e : α ≃ β) : β ≃ α := begin
    cases e with f H, have q := qinv.b2q f H,
    cases q with g qinv, cases qinv with α β,
    existsi g, split; existsi f,
    exact α, exact β
  end
end equiv

end ground_zero