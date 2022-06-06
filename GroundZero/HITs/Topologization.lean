import GroundZero.Algebra.Reals
open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.HITs
  universe u v w

  inductive D.core (α : Type u) (ρ : α → α → Type v)
  | ε           : α → core α ρ
  | ρ {a b : α} : ρ a b → (𝕀 → core α ρ)

  inductive D.rel (α : Type u) (ρ : α → α → Type v) : D.core α ρ → D.core α ρ → Type (max u v)
  | η₀ {a b : α} (R : ρ a b) : rel α ρ (D.core.ρ R 0) (D.core.ε a)
  | η₁ {a b : α} (R : ρ a b) : rel α ρ (D.core.ρ R 1) (D.core.ε b)

  def D (α : Type u) (ρ : α → α → Type v) := Graph (D.rel α ρ)

  section
    variable {α : Type u} {r : α → α → Type v}
    hott def D.ε : α → D α r := Graph.elem ∘ D.core.ε
    hott def D.ρ {a b : α} (R : r a b) : 𝕀 → D α r := Graph.elem ∘ D.core.ρ R

    noncomputable hott def D.η₀ {a b : α} (R : r a b) : D.ρ R 0 = D.ε a :=
    Graph.line (D.rel.η₀ R)

    noncomputable hott def D.η₁ {a b : α} (R : r a b) : D.ρ R 1 = D.ε b :=
    Graph.line (D.rel.η₁ R)
  end
end GroundZero.HITs