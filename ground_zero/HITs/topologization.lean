import ground_zero.algebra.reals
open ground_zero.structures (hset zero_eqv_set)
open ground_zero.HITs (trunc)
open ground_zero.types
open ground_zero

hott theory

namespace ground_zero.HITs
  universes u v w

  inductive D.core (α : Type u) (ρ : α → α → Type v)
  | ε           : α → D.core
  | ρ {a b : α} : ρ a b → (𝕀 → D.core)

  inductive D.rel (α : Type u) (ρ : α → α → Type v) : D.core α ρ → D.core α ρ → Type (max u v)
  | η₀ {a b : α} (R : ρ a b) : D.rel (D.core.ρ R 0) (D.core.ε a)
  | η₁ {a b : α} (R : ρ a b) : D.rel (D.core.ρ R 1) (D.core.ε b)

  def D (α : Type u) (ρ : α → α → Type v) := graph (D.rel α ρ)

  section
    variables {α : Type u} {ρ : α → α → Type v}
    @[hott] def D.ε : α → D α ρ := graph.elem ∘ D.core.ε
    @[hott] def D.ρ {a b : α} (R : ρ a b) : 𝕀 → D α ρ := graph.elem ∘ D.core.ρ R

    @[hott] noncomputable def D.η₀ {a b : α} (R : ρ a b) : D.ρ R 0 = D.ε a :=
    graph.line (D.rel.η₀ R)

    @[hott] noncomputable def D.η₁ {a b : α} (R : ρ a b) : D.ρ R 1 = D.ε b :=
    graph.line (D.rel.η₁ R)
  end
end ground_zero.HITs