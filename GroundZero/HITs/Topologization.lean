import GroundZero.Algebra.Reals
open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.HITs
  universe u v w

  inductive D.core (A : Type u) (ρ : A → A → Type v)
  | ε           : A → core A ρ
  | ρ {a b : A} : ρ a b → (𝕀 → core A ρ)

  inductive D.rel (A : Type u) (ρ : A → A → Type v) : D.core A ρ → D.core A ρ → Type (max u v)
  | η₀ {a b : A} (R : ρ a b) : rel A ρ (D.core.ρ R 0) (D.core.ε a)
  | η₁ {a b : A} (R : ρ a b) : rel A ρ (D.core.ρ R 1) (D.core.ε b)

  def D (A : Type u) (ρ : A → A → Type v) := Graph (D.rel A ρ)

  section
    variable {A : Type u} {r : A → A → Type v}
    hott def D.ε : A → D A r := Graph.elem ∘ D.core.ε
    hott def D.ρ {a b : A} (R : r a b) : 𝕀 → D A r := Graph.elem ∘ D.core.ρ R

    noncomputable hott def D.η₀ {a b : A} (R : r a b) : D.ρ R 0 = D.ε a :=
    Graph.line (D.rel.η₀ R)

    noncomputable hott def D.η₁ {a b : A} (R : r a b) : D.ρ R 1 = D.ε b :=
    Graph.line (D.rel.η₁ R)
  end
end GroundZero.HITs