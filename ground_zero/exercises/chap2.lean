import ground_zero.types.sigma
import ground_zero.structures

open ground_zero ground_zero.types
open ground_zero.types.equiv
open ground_zero.proto

open ground_zero.structures (prop contr)

universes u v u' v' w k
hott theory

-- exercise 2.1

section
  variables {α : Type u} {a b c : α}

  @[hott] def trans₁ (p : a = b) (q : b = c) : a = c :=
  @Id.rec α a (λ x _, x = c → a = c) (@Id.rec α a (λ x _, a = x) (idp a) c) b p q

  infixl ` ⬝₁ `:99 := trans₁

  @[hott] def trans₂ (p : a = b) (q : b = c) : a = c :=
  @Id.rec α a (λ x _, x = c → a = c) idfun b p q

  infixl ` ⬝₂ `:99 := trans₂

  @[hott] def trans₃ (p : a = b) (q : b = c) : a = c :=
  @Id.rec α b (λ x _, a = b → a = x) idfun c q p

  infixl ` ⬝₃ `:99 := trans₃

  @[hott] def eq₁₂ (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₂ q :=
  begin induction p, induction q, reflexivity end

  @[hott] def eq₂₃ (p : a = b) (q : b = c) : p ⬝₂ q = p ⬝₃ q :=
  begin induction p, induction q, reflexivity end

  @[hott] def eq₁₃ (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₃ q :=
  begin induction p, induction q, reflexivity end
end

-- exercise 2.2

section
  variables {α : Type u} {a b c : α} (p : a = b) (q : b = c)

  @[hott] example : eq₁₂ p q ⬝ eq₂₃ p q = eq₁₃ p q :=
  begin induction p, induction q, reflexivity end
end

-- exercise 2.3

section
  variables {α : Type u} {a b c : α}

  @[hott] def trans₄ (p : a = b) (q : b = c) : a = c :=
  @Id.rec α b (λ x _, a = b → a = x) (@Id.rec α a (λ x _, a = x) (idp a) b) c q p

  infixl ` ⬝₄ `:99 := trans₄

  /-
  example (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₄ q := idp _
  example (p : a = b) (q : b = c) : p ⬝₂ q = p ⬝₄ q := idp _
  example (p : a = b) (q : b = c) : p ⬝₃ q = p ⬝₄ q := idp _
  -/

  @[hott] example (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₄ q :=
  begin induction p, induction q, reflexivity end
end

-- exercise 2.4

@[hott] def n_path (α : Type u) : ℕ → Type u
|    0    := α
| (n + 1) := Σ (a b : n_path n), a = b

notation n `-Path` := λ α, n_path α n

@[hott] def boundary {α : Type u} {n : ℕ} : (n + 1)-Path α → (n-Path α) × (n-Path α) :=
λ ⟨a, b, _⟩, (a, b)

-- exercise 2.5

namespace «2.5»
  variables {α : Type u} {β : Type v} {x y : α} (p : x = y)

  @[hott] def transconst (b : β) : transport (λ _, β) p b = b :=
  begin induction p, reflexivity end

  @[hott] def f (φ : α → β) :
    φ x = φ y → transport (λ _, β) p (φ x) = φ y :=
  λ q, transconst p (φ x) ⬝ q

  @[hott] def g (φ : α → β) :
    transport (λ _, β) p (φ x) = φ y → φ x = φ y :=
  λ q, (transconst p (φ x))⁻¹ ⬝ q

  @[hott] example (φ : α → β) : f p φ ∘ g p φ ~ id :=
  begin induction p, reflexivity end

  @[hott] example (φ : α → β) : g p φ ∘ f p φ ~ id :=
  begin induction p, reflexivity end
end «2.5»

-- exercise 2.6

@[hott] example {α : Type u} {x y z : α} (p : x = y) : biinv (@Id.trans α x y z p) :=
begin split; existsi (Id.trans p⁻¹); intro q; induction p; induction q; reflexivity end

-- exercise 2.7

namespace «2.7»
  variables {α : Type u} {α' : Type u'} {β : α → Type v} {β' : α' → Type v'}
            (g : α → α') (h : Π a, β a → β' (g a))

  def φ (x : Σ a, β a) : Σ a', β' a' := ⟨g x.1, h x.1 x.2⟩

  @[hott] example (x y : Σ a, β a) (p : x.1 = y.1) (q : x.2 =[p] y.2) :
      Id.map (φ g h) (sigma.prod p q)
    = @sigma.prod α' β' (φ g h x) (φ g h y)
        (@Id.map α α' x.1 y.1 g p) (dep_path_map' g h q) :=
  begin
    induction x with x u, induction y with y v,
    change x = y at p, induction p,
    change u = v at q, induction q,
    reflexivity
  end
end «2.7»