import ground_zero.algebra.group ground_zero.HITs.circle
open ground_zero.structures ground_zero.types.equiv
open ground_zero.types ground_zero.HITs

hott theory

namespace ground_zero.algebra

noncomputable def Z.magma : magma :=
⟨zeroeqv (transport hset circle.fundamental_group⁻¹ (λ _ _, integer.set)), Id.trans⟩

noncomputable def Z.semigroup : semigroup :=
⟨Z.magma, λ a b c, (Id.assoc a b c)⁻¹⟩

noncomputable def Z.monoid : monoid :=
⟨Z.semigroup, Id.refl, Id.refl_left, Id.refl_right⟩

noncomputable def Z : group :=
⟨Z.monoid, Id.inv, Id.inv_comp⟩

noncomputable instance Z.abelian : abelian Z :=
⟨circle.comm⟩

@[hott] def helix {G : group} (z : G.carrier) : S¹ → Type :=
circle.rec G.carrier (ground_zero.ua (group.left G z))

@[hott] def power {G : group} (z : G.carrier) (p : Z.carrier) : G.carrier :=
@transport S¹ (helix z) circle.base circle.base p G.e

-- In cubicaltt these two lemmas will just compute
@[hott] noncomputable def helix.mul {G : group} (z x : G.carrier) :
  transport (helix z) circle.loop x = G.φ z x :=
begin
  transitivity, apply equiv.transport_to_transportconst,
  transitivity, apply Id.map (λ p, transportconst p x),
  apply circle.recβrule₂, apply ground_zero.ua.transportconst_rule
end

@[hott] noncomputable def helix.mul_inv {G : group} (z x : G.carrier) :
  transport (helix z) circle.loop⁻¹ x = G.φ (G.inv z) x :=
begin
  transitivity, apply equiv.transport_to_transportconst,
  transitivity, apply Id.map (λ p, transportconst p x),
  transitivity, apply Id.map_inv, apply Id.map, apply circle.recβrule₂,
  transitivity, apply equiv.transportconst_over_inv,
  apply ground_zero.ua.transportconst_inv_rule
end

@[hott] noncomputable def power.succ {G : group} (z : G.carrier) :
  Π p, power z (circle.succ p) = G.φ z (power z p) :=
begin intro p, transitivity, apply equiv.subst_comp, apply helix.mul end

@[hott] noncomputable def power.pred {G : group} (z : G.carrier) :
  Π p, power z (circle.pred p) = G.φ (G.inv z) (power z p) :=
begin intro p, transitivity, apply equiv.subst_comp, apply helix.mul_inv end

@[hott] noncomputable def power.mul {G : group} (z : G.carrier)
  (p q : Z.carrier) : power z (p ⬝ q) = G.φ (power z p) (power z q) :=
begin
  fapply circle.Ωind₁ _ _ _ p; clear p,
  { symmetry, apply G.one_mul },
  repeat {
    intros p ih, transitivity, apply Id.map,
    transitivity, apply Id.map (⬝ q), apply circle.comm,
    transitivity, symmetry, apply Id.assoc, apply circle.comm
  },
  { transitivity, apply power.succ,
    transitivity, apply Id.map (G.φ z), apply ih,
    transitivity, symmetry, apply G.mul_assoc,
    apply Id.map (λ x, G.φ x (power z q)),
    symmetry, apply power.succ },
  { transitivity, apply power.pred,
    transitivity, apply Id.map (G.φ (G.inv z)), apply ih,
    transitivity, symmetry, apply G.mul_assoc,
    apply Id.map (λ x, G.φ x (power z q)),
    symmetry, apply power.pred }
end

@[hott] noncomputable def Z.rec {G : group} (z : G.carrier) : Z ⤳ G :=
⟨power z, power.mul z⟩

end ground_zero.algebra