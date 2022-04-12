import ground_zero.algebra.reals
open ground_zero.structures (hset)
open ground_zero.HITs (trunc)

hott theory

namespace ground_zero.HITs
  universe u

  inductive D.core (α : Type u)
  | ε : α → D.core
  | ρ : (I → α) → (𝕀 → D.core)

  inductive D.rel (α : Type u) : D.core α → D.core α → Type u
  | η₀ (φ : I → α) : D.rel (D.core.ρ φ 0) (D.core.ε (φ 0))
  | η₁ (φ : I → α) : D.rel (D.core.ρ φ 1) (D.core.ε (φ 1))

  def D (α : Type u) := ∥graph (D.rel α)∥₀

  def D.ε {α : Type u} : α → D α := trunc.elem ∘ graph.elem ∘ D.core.ε
  def D.ρ {α : Type u} (φ : I → α) : 𝕀 → D α := trunc.elem ∘ graph.elem ∘ D.core.ρ φ

  noncomputable def D.η₀ {α : Type u} (φ : I → α) : D.ρ φ 0 = D.ε (φ 0) := trunc.elem # (graph.line (D.rel.η₀ φ))
  noncomputable def D.η₁ {α : Type u} (φ : I → α) : D.ρ φ 1 = D.ε (φ 1) := trunc.elem # (graph.line (D.rel.η₁ φ))
end ground_zero.HITs