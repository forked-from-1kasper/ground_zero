import ground_zero.types.product
import ground_zero.theorems.nat
import ground_zero.types.sigma

open ground_zero ground_zero.types
open ground_zero.types.equiv
open ground_zero.proto

universes u v w k
hott theory

-- exercise 1.1

@[hott] def comp_assoc {α : Type u} {β : Type v} {γ : Type w} {δ : Type k}
  (f : α → β) (g : β → γ) (h : γ → δ) : h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
by reflexivity

-- exercise 1.2

@[hott] def product.rec' {α : Type u} {β : Type v} {γ : Type w}
  (φ : α → β → γ) : α × β → γ :=
λ u, φ u.1 u.2

@[hott] example {α : Type u} {β : Type v} {γ : Type w}
  (φ : α → β → γ) (a : α) (b : β) :
    product.rec' φ (a, b) = φ a b :=
by reflexivity

@[hott] def sigma.rec' {α : Type u} {β : α → Type v} {γ : Type w}
  (φ : Π x, β x → γ) : (Σ x, β x) → γ :=
λ u, φ u.1 u.2

@[hott] example {α : Type u} {β : α → Type v} {γ : Type w}
  (φ : Π x, β x → γ) (a : α) (b : β a) :
    sigma.rec' φ ⟨a, b⟩ = φ a b :=
by reflexivity

-- exercise 1.3

@[hott] def product.ind' {α : Type u} {β : Type v} {π : α × β → Type w}
  (φ : Π a b, π (a, b)) : Π x, π x :=
λ u, transport π (product.uniq u) (φ u.1 u.2)

@[hott] example {α : Type u} {β : Type v} {π : α × β → Type w}
  (φ : Π a b, π (a, b)) (a : α) (b : β) : product.ind' φ (a, b) = φ a b :=
by reflexivity

@[hott] def sigma.ind' {α : Type u} {β : α → Type v} {π : (Σ x, β x) → Type w}
  (φ : Π a b, π ⟨a, b⟩) : Π x, π x :=
λ u, transport π (sigma.uniq u) (φ u.1 u.2)

@[hott] example {α : Type u} {β : α → Type v} {π : (Σ x, β x) → Type w}
  (φ : Π a b, π ⟨a, b⟩) (a : α) (b : β a) : sigma.ind' φ ⟨a, b⟩ = φ a b :=
by reflexivity

-- exercise 1.4

@[hott] def nat.iter {C : Type u} (c₀ : C) (cₛ : C → C) : ℕ → C
|    0    := c₀
| (n + 1) := cₛ (nat.iter n)

@[hott] def grec {C : Type u} (c₀ : C) (cₛ : ℕ → C → C) : ℕ → ℕ × C :=
@nat.iter (ℕ × C) (0, c₀) (λ u, (u.1 + 1, cₛ u.1 u.2))

@[hott] def grec.stable {C : Type u} (c₀ : C) (cₛ : ℕ → C → C)
  (n : ℕ) : (grec c₀ cₛ n).1 = n :=
begin
  induction n with n ih, { reflexivity },
  { apply Id.map nat.succ, exact ih }
end

section
  variables {C : Type u} (c₀ : C) (cₛ : ℕ → C → C)

  @[hott] def nat.rec' : ℕ → C := prod.pr₂ ∘ grec c₀ cₛ

  @[hott] def nat.iterβ₁ : nat.rec' c₀ cₛ 0 = c₀ :=
  by reflexivity

  @[hott] def nat.iterβ₂ (n : ℕ) : nat.rec' c₀ cₛ (n + 1) = cₛ n (nat.rec' c₀ cₛ n) :=
  Id.map (λ m, cₛ m (nat.rec' c₀ cₛ n)) (grec.stable c₀ cₛ n)
end

-- exercise 1.5

@[hott] def coproduct' (α β : Type u) :=
Σ (x : 𝟐), bool.elim α β x

namespace coproduct'
  variables {α β : Type u}

  def inl {α β : Type u} (a : α) : coproduct' α β := ⟨ff, a⟩
  def inr {α β : Type u} (b : β) : coproduct' α β := ⟨tt, b⟩

  variables (π : coproduct' α β → Type v)
            (u : Π a, π (inl a))
            (v : Π b, π (inr b))

  @[hott] def ind : Π x, π x
  | ⟨ff, a⟩ := u a | ⟨tt, b⟩ := v b

  @[hott] def indβ₁ (a : α) : ind π u v (inl a) = u a :=
  by reflexivity

  @[hott] def indβ₂ (b : β) : ind π u v (inr b) = v b :=
  by reflexivity
end coproduct'

-- exercise 1.6

@[hott] def product' (α β : Type u) :=
Π (x : 𝟐), bool.elim α β x

namespace product'
  variables {α β : Type u}

  def mk (a : α) (b : β) : product' α β :=
  @bool.rec (bool.elim α β) a b

  def pr₁ : product' α β → α := λ u, u ff
  def pr₂ : product' α β → β := λ u, u tt

  def η (x : product' α β) : mk (pr₁ x) (pr₂ x) = x :=
  begin apply theorems.funext, intro b, induction b; reflexivity end

  variables (π : product' α β → Type v) (φ : Π a b, π (mk a b))

  @[hott] def ind : Π x, π x :=
  λ x, transport π (η x) (φ (pr₁ x) (pr₂ x))

  @[hott] def indβ (a : α) (b : β) : ind π φ (mk a b) = φ a b :=
  begin
    transitivity, apply Id.map (λ p, transport π p (φ a b)),
    transitivity, apply Id.map theorems.funext, change _ = (λ x, idp (mk a b x)),
    apply theorems.funext, intro b, induction b; reflexivity,
    apply theorems.funext_id, reflexivity
  end
end product'
