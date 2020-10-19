import ground_zero.types.ens
open ground_zero.structures

hott theory

namespace ground_zero

universes u v

namespace types

@[hott] def iseqclass {α : Type u} (R : eqrel α) (φ : ens α) :=
φ.inh × (Π x y, R.apply x y → x ∈ φ → y ∈ φ) × (Π x y, x ∈ φ → y ∈ φ → R.apply x y)

@[hott] def iseqclass.prop {α : Type u} {R : eqrel α} (φ : ens α) : prop (iseqclass R φ) :=
begin
  apply product_prop, apply HITs.merely.uniq,
  apply product_prop; repeat { apply pi_prop, intro },
  apply ens.prop, apply R.prop
end

@[hott] def setquot {α : Type u} (R : eqrel α) :=
Σ (φ : ens α), iseqclass R φ

@[hott] noncomputable def setquot.set {α : Type u} (R : eqrel α) : hset (setquot R) :=
begin
  fapply hset_respects_sigma, apply ens.isset,
  intro x, apply prop_is_set, apply iseqclass.prop
end

end types

end ground_zero