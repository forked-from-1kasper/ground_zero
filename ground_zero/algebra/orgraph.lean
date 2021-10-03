import ground_zero.algebra.basic

hott theory

namespace ground_zero.algebra
  universe u

  -- this is exactly directed graph
  def orgraph : Type (u + 1) :=
  @Alg.{0 0 0 u} ⊥ (𝟏 : Type) (λ _, 2)

  def orgraph.rel (Γ : orgraph) (x y : Γ.carrier) : Ω := Γ.rel ★ (x, y, ★)
  def orgraph.ρ (Γ : orgraph.{u}) (x y : Γ.carrier) : Type u := (Γ.rel x y).1

  class reflexive (Γ : orgraph) :=
  (refl : Π x, Γ.ρ x x)

  class symmetric (Γ : orgraph) :=
  (symm : Π x y, Γ.ρ x y → Γ.ρ y x)

  class transitive (Γ : orgraph) :=
  (trans : Π x y z, Γ.ρ x y → Γ.ρ y z → Γ.ρ x z)

  class equivalence (Γ : orgraph) extends reflexive Γ, symmetric Γ, transitive Γ

  class antisymmetric (Γ : orgraph) :=
  (asymm : Π x y, Γ.ρ x y → Γ.ρ y x → x = y)

  class order (Γ : orgraph) extends reflexive Γ, antisymmetric Γ, transitive Γ

  def exact (Γ : orgraph) (φ : Γ.carrier → Ω) (x : Γ.carrier) :=
  (φ x).1 × (Π y, (φ y).1 → Γ.ρ x y)

  def coexact (Γ : orgraph) (φ : Γ.carrier → Ω) (x : Γ.carrier) :=
  (φ x).1 × (Π y, (φ y).1 → Γ.ρ y x)
end ground_zero.algebra