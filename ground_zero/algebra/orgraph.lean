import ground_zero.algebra.ring

hott theory

namespace ground_zero.algebra
  universes u v

  -- this is exactly directed graph
  def orgraph : Type (max u v + 1) :=
  @Alg.{0 0 u v} ⊥ 𝟏 (λ _, 2)

  def orgraph.rel (Γ : orgraph) (x y : Γ.carrier) : Ω := Γ.rel ★ (x, y, ★)
  def orgraph.ρ (Γ : orgraph.{u}) (x y : Γ.carrier) : Type v := (Γ.rel x y).1

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

  def overring.κ (T : overring) : orgraph :=
  ⟨T.1, (by intro i; induction i, T.2.2)⟩

  class connected (Γ : orgraph) :=
  (total : Π x y, ∥Γ.ρ x y + Γ.ρ y x∥)

  class total (Γ : orgraph) extends order Γ, connected Γ

  class orfield (T : overring) extends field T.τ, total T.κ :=
  (le_over_add : Π (x y z : T.carrier), x ≤ y → x + z ≤ y + z)
  (le_over_mul : Π (x y : T.carrier), 0 ≤ x → 0 ≤ y → 0 ≤ x * y)
end ground_zero.algebra