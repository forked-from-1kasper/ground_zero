import ground_zero.theorems.classical
import ground_zero.algebra.ring
open ground_zero.structures (prop pi_prop)
open ground_zero.types ground_zero.proto
open ground_zero.HITs (merely)
open ground_zero.theorems

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

  @[hott] def eq_impl_refl_rel (Γ : orgraph) [reflexive Γ] (a b : Γ.carrier) : a = b → Γ.ρ a b :=
  begin intro p, induction p, apply reflexive.refl end

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
  (total : Π x y, merely (Γ.ρ x y + Γ.ρ y x))

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

  def majorized {Γ : orgraph} (φ : Γ.subset) := merely (Σ M, majorant φ M)
  def minorized {Γ : orgraph} (φ : Γ.subset) := merely (Σ m, majorant φ m)

  def exactness {Γ : orgraph} (φ : Γ.subset) := merely (Σ M, exact φ M)
  def coexactness {Γ : orgraph} (φ : Γ.subset) := merely (Σ M, coexact φ M)

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

  @[hott] def le_over_add_left (T : overring) [orfield T] (a b c : T.carrier) (p : a ≤ b) : c + a ≤ c + b :=
  begin apply equiv.transportconst, apply equiv.bimap; apply T.τ⁺.mul_comm, apply orfield.le_over_add, exact p end

  @[hott] def ineq_add (T : overring) [orfield T] {a b c d : T.carrier} (p : a ≤ b) (q : c ≤ d) : a + c ≤ b + d :=
  begin apply @transitive.trans T.κ, apply orfield.le_over_add, exact p, apply le_over_add_left, exact q end

  @[hott] def lt_over_add (T : overring) [orfield T] (a b c : T.carrier) (p : a < b) : a + c < b + c :=
  begin
    split, intro q, apply p.1,
    apply equiv.transportconst, apply equiv.bimap,
    symmetry, apply @group.cancel_right T.τ⁺ _ a c,
    symmetry, apply @group.cancel_right T.τ⁺ _ b c,
    apply Id.map (λ x, x - c) q, apply orfield.le_over_add, exact p.2
  end

  @[hott] def lt_over_add_left (T : overring) [orfield T] (a b c : T.carrier) (p : a < b) : c + a < c + b :=
  begin apply equiv.transportconst, apply equiv.bimap; apply T.τ⁺.mul_comm, apply lt_over_add, exact p end

  @[hott] def strict_ineq_trans_right (T : overring) [orfield T] {a b c : T.carrier} (p : a < b) (q : b ≤ c) : a < c :=
  begin
    split, intro r, apply p.1, apply @antisymmetric.asymm T.κ, apply p.2,
    apply equiv.transport (T.ρ b), exact r⁻¹, assumption,
    apply @transitive.trans T.κ, exact p.2, exact q
  end

  @[hott] def strict_ineq_trans_left (T : overring) [orfield T] {a b c : T.carrier} (p : a ≤ b) (q : b < c) : a < c :=
  begin
    split, intro r, apply q.1, apply @antisymmetric.asymm T.κ, apply q.2,
    apply equiv.transport (λ x, T.ρ x b), exact r, assumption,
    apply @transitive.trans T.κ, exact p, exact q.2
  end

  @[hott] def strict_ineq_trans (T : overring) [orfield T] {a b c : T.carrier} (p : a < b) (q : b < c) : a < c :=
  strict_ineq_trans_left T p.2 q

  @[hott] def strict_ineq_add (T : overring) [orfield T] {a b c d : T.carrier} (p : a < b) (q : c < d) : a + c < b + d :=
  begin apply strict_ineq_trans, apply lt_over_add, exact p, apply lt_over_add_left, exact q end

  @[hott] def strict_ineq_add_left (T : overring) [orfield T] {a b c d : T.carrier} (p : a ≤ b) (q : c < d) : a + c < b + d :=
  begin apply strict_ineq_trans_left, apply orfield.le_over_add, exact p, apply lt_over_add_left, exact q end

  @[hott] def strict_ineq_add_right (T : overring) [orfield T] {a b c d : T.carrier} (p : a < b) (q : c ≤ d) : a + c < b + d :=
  begin apply strict_ineq_trans_right, apply lt_over_add, exact p, apply le_over_add_left, exact q end

  @[hott] noncomputable def minus_inv_sign (T : overring) [orfield T] (a b : T.carrier) (p : a ≤ b) : -a ≥ -b :=
  begin
    fapply ground_zero.HITs.merely.rec _ _ (connected.total _ _), exact T.κ,
    change T.carrier, exact -b, change T.carrier, exact -a, apply T.κ.prop,
    { intro ih, induction ih with p q, exact p,
      cases @classical.lem (a = b) T.hset with r₁ r₂,
      apply eq_impl_refl_rel T.κ, symmetry, apply Id.map T.τ.neg r₁,
      apply empty.elim, apply (_ : T.σ 0 0).1, reflexivity,
      apply equiv.transportconst, apply equiv.bimap,
      apply @group.mul_right_inv T.τ⁺, exact a,
      apply @group.mul_right_inv T.τ⁺, exact b,
      apply strict_ineq_add_right, exact (r₂, p), exact q },
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