import ground_zero.types.ens
open ground_zero.structures

hott theory

namespace ground_zero

universes u v w

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

@[hott] def setquot.elem {α : Type u} {R : eqrel α} (x : α) : setquot R :=
⟨⟨λ y, R.apply x y, R.prop x⟩,
  (HITs.merely.elem ⟨x, R.refl x⟩,
   λ a b p q, R.trans q p,
   λ a b p q, R.trans (R.symm p) q)⟩

@[hott] noncomputable def setquot.sound {α : Type u} {R : eqrel α} {x y : α} :
  R.apply x y → setquot.elem x = setquot.elem y :> setquot R :=
begin
  intro p, fapply types.sigma.prod,
  { apply ens.ext, intro z, split; intro q,
    { apply R.trans, exact R.symm p, exact q },
    { apply R.trans, exact p, exact q } },
  { apply iseqclass.prop }
end

end types

end ground_zero