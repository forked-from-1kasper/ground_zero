import ground_zero.algebra.reals
open ground_zero.structures (hset zero_eqv_set)
open ground_zero.HITs (trunc)
open ground_zero.types
open ground_zero

hott theory

namespace ground_zero.HITs
  universes u v w

  inductive D.core (α : Type u)
  | ε           : α → D.core
  | ρ {a b : α} : a = b → (𝕀 → D.core)

  -- TODO
  axiom neg : 𝕀 → 𝕀
  axiom concat {α : Type u} : (𝕀 → α) → (𝕀 → α) → (𝕀 → α)

  inductive D.rel (α : Type u) : D.core α → D.core α → Type u
  | η₀ {a b : α} (p : a = b)                       : D.rel (D.core.ρ p 0) (D.core.ε a)
  | η₁ {a b : α} (p : a = b)                       : D.rel (D.core.ρ p 1) (D.core.ε b)
  | κ₁ (a : α) (r : 𝕀)                             : D.rel (D.core.ρ (idp a) r) (D.core.ε a)
  | κ₂ {a b : α} (p : a = b) (r : 𝕀)               : D.rel (D.core.ρ p⁻¹ r) (D.core.ρ p (neg r))
  | κ₃ {a b c : α} (p : a = b) (q : b = c) (r : 𝕀) : D.rel (D.core.ρ (p ⬝ q) r) (concat (D.core.ρ p) (D.core.ρ q) r)

  def D (α : Type u) := ∥graph (D.rel α)∥₀

  def D.ε {α : Type u} : α → D α := trunc.elem ∘ graph.elem ∘ D.core.ε
  def D.ρ {α : Type u} {a b : α} (p : a = b) : 𝕀 → D α := trunc.elem ∘ graph.elem ∘ D.core.ρ p

  @[hott] noncomputable def D.η₀ {α : Type u} {a b : α} (p : a = b) : D.ρ p 0 = D.ε a :=
  trunc.elem # (graph.line (D.rel.η₀ p))

  @[hott] noncomputable def D.η₁ {α : Type u} {a b : α} (p : a = b) : D.ρ p 1 = D.ε b :=
  trunc.elem # (graph.line (D.rel.η₁ p))

  @[hott] def D.κ₁ {α : Type u} (a : α) (r : 𝕀) : D.ρ (idp a) r = D.ε a :=
  trunc.elem # (graph.line (D.rel.κ₁ a r))

  @[hott] noncomputable def D.κ₂ {α : Type u} {a b : α} (p : a = b) (r : 𝕀) : D.ρ p⁻¹ r = D.ρ p (neg r) :=
  trunc.elem # (graph.line (D.rel.κ₂ p r))
end ground_zero.HITs