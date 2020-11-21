import ground_zero.algebra.group
open ground_zero.structures
open ground_zero.types

hott theory

namespace ground_zero.algebra
  structure gis (M : Type) (G : group) :=
  (ι     : M → M → G.carrier)
  (trans : Π x y z, G.φ (ι x y) (ι y z) = ι x z)
  (full  : Π g x, contr (Σ y, ι x y = g))

  namespace gis
    variables {M : Type} {G : group} (L : gis M G)

    local infix ` * ` := G.φ
    local postfix ⁻¹ := G.inv

    @[hott] def neut : Π x, L.ι x x = G.e :=
    begin intro x, apply group.unit_of_sqr, apply L.trans end

    @[hott] def inv : Π x y, (L.ι x y)⁻¹ = L.ι y x :=
    begin
      intros x y, apply group.inv_eq_of_mul_eq_one,
      transitivity, apply L.trans, apply gis.neut
    end

    @[hott] def propι : Π g x, prop (Σ y, L.ι x y = g) :=
    λ g x, contr_impl_prop (L.full g x)

    @[hott] def zero : Π x y, L.ι x y = G.e → x = y :=
    begin
      intros x y p, symmetry,
      have r := L.propι (L.ι x y) x ⟨y, Id.refl⟩ ⟨x, L.neut x ⬝ Id.inv p⟩,
      apply (sigma.sigma_eq_of_eq r).fst
    end
  end gis
end ground_zero.algebra