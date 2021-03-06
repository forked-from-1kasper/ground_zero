import ground_zero.algebra.group ground_zero.HITs.circle
open ground_zero.structures ground_zero.types.equiv
open ground_zero.types ground_zero.HITs
open ground_zero.algebra.group (S)

hott theory

namespace ground_zero.algebra

noncomputable def ZΩ : pregroup :=
pregroup.intro (transport hset circle.fundamental_group⁻¹ (λ _ _, integer.set))
  Id.trans Id.inv Id.refl

noncomputable instance ZΩ.semigroup : semigroup ZΩ.magma :=
⟨λ a b c, (Id.assoc a b c)⁻¹⟩

noncomputable instance ZΩ.monoid : monoid ZΩ.premonoid :=
⟨ZΩ.semigroup, Id.refl_left, Id.refl_right⟩

noncomputable instance ZΩ.group : group ZΩ :=
⟨ZΩ.monoid, Id.inv_comp⟩

noncomputable instance ZΩ.abelian : abelian ZΩ :=
⟨circle.comm⟩

@[hott] def helix {G : pregroup} [group G] (z : G.carrier) : S¹ → Type :=
circle.rec G.carrier (ground_zero.ua (group.left G z))

@[hott] def power {G : pregroup} [group G]
  (z : G.carrier) (p : ZΩ.carrier) : G.carrier :=
@transport S¹ (helix z) circle.base circle.base p G.e

-- In cubicaltt these two lemmas will just compute
@[hott] noncomputable def helix.loop {G : pregroup} [group G] (z x : G.carrier) :
  transport (helix z) circle.loop x = G.φ z x :=
begin
  transitivity, apply equiv.transport_to_transportconst,
  transitivity, apply Id.map (λ p, transportconst p x),
  apply circle.recβrule₂, apply ground_zero.ua.transportconst_rule
end

@[hott] noncomputable def helix.loop_inv {G : pregroup} [group G] (z x : G.carrier) :
  transport (helix z) circle.loop⁻¹ x = G.φ (G.ι z) x :=
begin
  transitivity, apply equiv.transport_to_transportconst,
  transitivity, apply Id.map (λ p, transportconst p x),
  transitivity, apply Id.map_inv, apply Id.map, apply circle.recβrule₂,
  transitivity, apply equiv.transportconst_over_inv,
  apply ground_zero.ua.transportconst_inv_rule
end

@[hott] noncomputable def power.succ {G : pregroup} [group G] (z : G.carrier) :
  Π p, power z (circle.succ p) = G.φ z (power z p) :=
begin intro p, transitivity, apply equiv.subst_comp, apply helix.loop end

@[hott] noncomputable def power.pred {G : pregroup} [group G] (z : G.carrier) :
  Π p, power z (circle.pred p) = G.φ (G.ι z) (power z p) :=
begin intro p, transitivity, apply equiv.subst_comp, apply helix.loop_inv end

@[hott] noncomputable def power.mul {G : pregroup} [group G] (z : G.carrier)
  (p q : ZΩ.carrier) : power z (p ⬝ q) = G.φ (power z p) (power z q) :=
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
    transitivity, apply Id.map (G.φ (G.ι z)), apply ih,
    transitivity, symmetry, apply G.mul_assoc,
    apply Id.map (λ x, G.φ x (power z q)),
    symmetry, apply power.pred }
end

@[hott] noncomputable def ZΩ.rec {G : pregroup} [group G]
  (z : G.carrier) : ZΩ ⤳ G :=
group.mkhomo (power z) (power.mul z)

@[hott] noncomputable def ZΩ.mul (p q : ZΩ.carrier) : ZΩ.carrier :=
(@power (S ZΩ.zero) _ (group.left ZΩ p) q).fst Id.refl

@[hott] noncomputable def power.one {G : pregroup} [group G] :
  Π p, power G.e p = G.e :=
begin
  fapply circle.Ωind₁, { trivial },
  { intros x ih, transitivity, apply power.succ,
    transitivity, apply G.one_mul, exact ih },
  { intros x ih, transitivity, apply power.pred,
    transitivity, apply Id.map (λ y, G.φ y (power G.e x)),
    symmetry, apply group.unit_inv,
    transitivity, apply G.one_mul, exact ih }
end

@[hott] def power.zero {G : pregroup} [group G]
  (x : G.carrier) : power x Id.refl = G.e :=
by reflexivity

@[hott] noncomputable def ZΩ.mul_zero (p : ZΩ.carrier) :
  ZΩ.mul p Id.refl = Id.refl :=
by trivial

@[hott] noncomputable def ZΩ.zero_mul (p : ZΩ.carrier) :
  ZΩ.mul Id.refl p = Id.refl :=
@Id.map (S ZΩ.zero).carrier ZΩ.carrier _ _ (λ e, e.fst Id.refl) (power.one p)

end ground_zero.algebra