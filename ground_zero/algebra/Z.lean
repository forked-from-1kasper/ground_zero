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

end ground_zero.algebra