import ground_zero.algebra.basic

open ground_zero.structures (prop propset contr)
open ground_zero.types ground_zero.proto
open ground_zero.HITs

hott theory

namespace ground_zero.algebra
  universes u v

  def pregeometry : Type (max u v + 1) :=
  @Alg.{0 0 u v} 𝟎 𝟐 (coproduct.elim empty.elim (bool.rec 3 4))

  namespace pregeometry
    def segment (G : pregeometry) :=
    G.carrier × G.carrier

    def between (G : pregeometry) (a b c : G.carrier) :=
    (G.rel ff (a, b, c, ★)).1

    def congruent (G : pregeometry) (a b c d : G.carrier) :=
    (G.rel tt (a, b, c, d, ★)).1

    def prop₁ (G : pregeometry) {a b c : G.carrier} : prop (G.between a b c) :=
    (G.rel ff (a, b, c, ★)).2

    def prop₂ (G : pregeometry) {a b c d : G.carrier} : prop (G.congruent a b c d) :=
    (G.rel tt (a, b, c, d, ★)).2

    @[hott] def collinear (G : pregeometry) (a b c : G.carrier) :=
    merely (G.between a b c + G.between c a b + G.between b c a)
  end pregeometry

  class geometry (G : pregeometry) :=
  (refl  : Π a b, G.congruent a b b a)
  (trans : Π a₁ b₁ a₂ b₂ a₃ b₃, G.congruent a₁ b₁ a₂ b₂ → G.congruent a₁ b₁ a₃ b₃ → G.congruent a₂ b₂ a₃ b₃)
  (idp₁  : Π a b c, G.congruent a b c c → a = b)
  (idp₂  : Π a b, G.between a b a → a = b)
  (pasch : Π a b c u v, G.between a u c → G.between b v c → merely (Σ x, G.between u x b × G.between v x a))

  class nonlinear (G : pregeometry) :=
  (lower : merely (Σ a b c, (¬G.between a b c) × (¬G.between b c a) × (¬G.between c a b)))

  class planar (G : pregeometry) :=
  (upper : Π a b c u v, G.congruent a u a v → G.congruent b u b v → G.congruent c u c v → ¬(u = v) → G.collinear a b c)

  class planimetry (G : pregeometry) extends geometry G, nonlinear G, planar G

  class isotropic (G : pregeometry) :=
  (construct : Π a b x y, merely (Σ z, G.between x y z × G.congruent y z a b))

  class continuous (G : pregeometry) :=
  (cut (φ ψ : G.carrier → propset) :
    merely (Σ a, Π x y, (φ x).1 → (ψ y).1 → G.between a x y) →
    merely (Σ b, Π x y, (φ x).1 → (ψ y).1 → G.between x b y))

  class absolute (G : pregeometry) extends geometry G, isotropic G :=
  (five : Π x₁ y₁ z₁ u₁ x₂ y₂ z₂ u₂, ¬(x₁ = y₁) → G.between x₁ y₁ z₁ → G.between x₂ y₂ z₂ →
    G.congruent x₁ y₁ x₂ y₂ → G.congruent y₁ z₁ y₂ z₂ →
    G.congruent x₁ u₁ x₂ u₂ → G.congruent y₁ u₁ y₂ u₂ →
    G.congruent z₁ u₁ z₂ u₂)

  @[hott] def segment (G : pregeometry) (a b : G.carrier) : ens G.carrier :=
  ⟨λ c, G.between a c b, λ _, G.prop₁⟩

  @[hott] def geodesic (G : pregeometry) (a b : G.carrier) : ens G.carrier :=
  ⟨G.collinear a b, λ _, merely.uniq⟩

  @[hott] def circle (G : pregeometry) (a b : G.carrier) : ens G.carrier :=
  ⟨λ c, G.congruent a b a c, λ _, G.prop₂⟩

  @[hott] def triangle (G : pregeometry) (a b c : G.carrier) : ens G.carrier :=
  ⟨λ z, merely (G.between a z b + G.between b z c + G.between a z c), λ _, merely.uniq⟩

  @[hott] def ray (G : pregeometry) (a b : G.carrier) : ens G.carrier :=
  ⟨λ c, merely (G.between a c b + G.between a b c), λ _, merely.uniq⟩

  class euclidean (G : pregeometry) extends absolute G :=
  (fifth : Π a₁ b₁ a₂ b₂ a₃ b₃,
    ens.parallel (geodesic G a₁ b₁) (geodesic G a₃ b₃) →
    ens.parallel (geodesic G a₂ b₂) (geodesic G a₃ b₃) →
    ens.parallel (geodesic G a₁ b₁) (geodesic G a₂ b₂))
end ground_zero.algebra