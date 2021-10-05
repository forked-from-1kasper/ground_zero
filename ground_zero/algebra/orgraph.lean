import ground_zero.algebra.ring
open ground_zero.structures (prop pi_prop)
open ground_zero.types
open ground_zero.proto

hott theory

namespace ground_zero.algebra
  universes u v

  -- this is exactly directed graph
  def orgraph : Type (max u v + 1) :=
  @Alg.{0 0 u v} ⊥ 𝟏 (λ _, 2)

  def orgraph.rel (Γ : orgraph) (x y : Γ.carrier) : Ω := Γ.rel ★ (x, y, ★)
  def orgraph.ρ (Γ : orgraph.{u}) (x y : Γ.carrier) : Type v := (Γ.rel x y).1

  def orgraph.prop (Γ : orgraph.{u}) (x y : Γ.carrier) : prop (Γ.ρ x y) := (Γ.rel x y).2

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

  def overring.κ (T : overring) : orgraph :=
  ⟨T.1, (by intro i; induction i, T.2.2)⟩

  class connected (Γ : orgraph) :=
  (total : Π x y, ∥Γ.ρ x y + Γ.ρ y x∥)

  class total (Γ : orgraph) extends order Γ, connected Γ

  class orfield (T : overring) extends field T.τ, total T.κ :=
  (le_over_add : Π (x y z : T.carrier), x ≤ y → x + z ≤ y + z)
  (le_over_mul : Π (x y : T.carrier), 0 ≤ x → 0 ≤ y → 0 ≤ x * y)

  instance (T : overring) [H : orfield T] : has_one T.carrier := H.to_has_one

  def majorant {Γ : orgraph} (φ : Γ.subset) (M : Γ.carrier) :=
  Π x, x ∈ φ → Γ.ρ x M

  def minorant {Γ : orgraph} (φ : Γ.subset) (m : Γ.carrier) :=
  Π x, x ∈ φ → Γ.ρ m x

  def exact {Γ : orgraph} (φ : Γ.subset) (x : Γ.carrier) :=
  x ∈ φ × minorant φ x

  def coexact {Γ : orgraph} (φ : Γ.subset) (x : Γ.carrier) :=
  x ∈ φ × majorant φ x

  def majorized {Γ : orgraph} (φ : Γ.subset) := ∥(Σ M, majorant φ M)∥
  def minorized {Γ : orgraph} (φ : Γ.subset) := ∥(Σ m, majorant φ m)∥

  def exactness {Γ : orgraph} (φ : Γ.subset) := ∥(Σ M, exact φ M)∥
  def coexactness {Γ : orgraph} (φ : Γ.subset) := ∥(Σ M, coexact φ M)∥

  def bounded {Γ : orgraph} (φ : Γ.subset) :=
  majorized φ × minorized φ

  @[hott] def Majorant {Γ : orgraph} (φ : Γ.subset) : Γ.subset :=
  ⟨majorant φ, begin
    intro x, apply pi_prop,
    intro y, apply pi_prop,
    intro H, apply Γ.prop
  end⟩

  @[hott] def Minorant {Γ : orgraph} (φ : Γ.subset) : Γ.subset :=
  ⟨minorant φ, begin
    intro x, apply pi_prop,
    intro y, apply pi_prop,
    intro H, apply Γ.prop
  end⟩

  @[hott] def one_gt_zero (T : overring) [orfield T] : T.ρ 0 1 :=
  begin
    fapply ground_zero.HITs.merely.rec _ _ (connected.total _ _), exact T.κ,
    change T.carrier, exact 0, change T.carrier, exact 1, apply T.κ.prop,
    { intro ih, induction ih with p q, exact p, apply empty.elim,
      apply @field.nontrivial T.τ _, apply @antisymmetric.asymm T.κ,
      exact q, apply equiv.transport, apply ring.minus_one_sqr,
      apply orfield.le_over_mul;
      { apply equiv.transport (λ i, T.ρ i (-1)),
        apply @group.mul_right_inv T.τ⁺, change T.carrier, exact 1,
        apply equiv.transport, apply T.τ⁺.one_mul,
        apply orfield.le_over_add, exact q } },
    apply_instance
  end

  -- or complete at top
  class complete (Γ : orgraph) :=
  (sup : Π (φ : Γ.subset), φ.inh → majorized φ → exactness (Majorant φ))

  -- or complete at bottom
  class cocomplete (Γ : orgraph) :=
  (inf : Π (φ : Γ.subset), φ.inh → minorized φ → coexactness (Minorant φ))

  class dedekind (T : overring) extends orfield T, complete T.κ
end ground_zero.algebra