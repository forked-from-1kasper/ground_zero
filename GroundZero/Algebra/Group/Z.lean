import GroundZero.Algebra.Group.Symmetric
import GroundZero.HITs.Circle

open GroundZero.Structures GroundZero.Types.Equiv
open GroundZero.Types GroundZero.HITs

namespace GroundZero.Algebra

noncomputable def ZΩ : Group :=
Group.intro (Circle.isGroupoid Circle.base Circle.base) Id.trans Id.inv Id.refl
  (λ a b c, (Id.assoc a b c)⁻¹) Id.reflLeft Id.reflRight Id.invComp

noncomputable def ZΩ.abelian : ZΩ.isCommutative := Circle.comm

hott def helix {G : Group} (z : G.carrier) : S¹ → Type :=
Circle.rec G.carrier (GroundZero.ua (Group.left G z))

hott def power {G : Group} (z : G.carrier) (p : ZΩ.carrier) : G.carrier :=
@transport S¹ (helix z) Circle.base Circle.base p G.e

-- In cubicaltt these two lemmas will just compute
noncomputable hott def helix.loop {G : Group} (z x : G.carrier) :
  transport (helix z) Circle.loop x = G.φ z x :=
begin
  transitivity; apply Equiv.transportToTransportconst;
  transitivity; apply Id.map (transportconst · x);
  apply Circle.recβrule₂; apply ua.transportRule
end

noncomputable hott def helix.loopInv {G : Group} (z x : G.carrier) :
  transport (helix z) Circle.loop⁻¹ x = G.φ (G.ι z) x :=
begin
  transitivity; apply Equiv.transportToTransportconst;
  transitivity; apply Id.map (transportconst · x);
  transitivity; apply Id.mapInv; apply Id.map;
  apply Circle.recβrule₂; apply ua.transportInvRule
end

noncomputable hott def power.succ {G : Group} (z : G.carrier) :
  Π p, power z (Circle.succ p) = G.φ z (power z p) :=
begin intro p; transitivity; apply Equiv.substComp; apply helix.loop end

noncomputable hott def power.pred {G : Group} (z : G.carrier) :
  Π p, power z (Circle.pred p) = G.φ (G.ι z) (power z p) :=
begin intro p; transitivity; apply Equiv.substComp; apply helix.loopInv end

noncomputable hott def power.mul {G : Group} (z : G.carrier) :
  Π (p q : ZΩ.carrier), power z (p ⬝ q) = G.φ (power z p) (power z q) :=
begin
  intro p q; fapply @Circle.Ωind₁ (λ p, power z (p ⬝ q) = G.φ (power z p) (power z q)) <;> clear p;
  { symmetry; apply G.oneMul };
  { intros p ih; transitivity; apply Id.map; transitivity;
    symmetry; apply Id.assoc; transitivity; apply Id.map (Id.trans p);
    apply Circle.comm; apply Id.assoc; transitivity; apply power.succ;
    transitivity; apply Id.map (G.φ z); exact ih;
    transitivity; symmetry; apply G.mulAssoc;
    apply Id.map (G.φ · _); symmetry; apply power.succ };
  { intros p ih; transitivity; apply Id.map; transitivity;
    symmetry; apply Id.assoc; transitivity; apply Id.map (Id.trans p);
    apply Circle.comm; apply Id.assoc; transitivity; apply power.pred;
    transitivity; apply Id.map (G.φ (G.ι z)); exact ih;
    transitivity; symmetry; apply G.mulAssoc;
    apply Id.map (G.φ · _); symmetry; apply power.pred }
end

noncomputable hott def ZΩ.rec {G : Group} (z : G.carrier) : Group.Hom ZΩ G :=
Group.mkhomo (power z) (power.mul z)

noncomputable hott def ZΩ.mul (p q : ZΩ.carrier) : ZΩ.carrier :=
(@power (Group.S ZΩ.1.zero) (Group.left ZΩ p) q).1 Id.refl

noncomputable hott def power.one {G : Group} : Π p, power G.e p = G.e :=
begin
  fapply Circle.Ωind₁; reflexivity;
  { intros p ih; transitivity; apply power.succ;
    transitivity; apply G.oneMul; exact ih };
  { intros p ih; transitivity; apply power.pred;
    transitivity; apply Id.map (G.φ · _);
    symmetry; apply Group.unitInv;
    transitivity; apply G.oneMul; exact ih }
end

hott def power.zero {G : Group} (x : G.carrier) : power x Id.refl = G.e :=
by reflexivity

noncomputable hott def ZΩ.mulZero (p : ZΩ.carrier) :
  ZΩ.mul p Id.refl = Id.refl :=
by reflexivity

-- something is really wrong with this thing
--noncomputable hott def ZΩ.zeroMul (p : ZΩ.carrier) : ZΩ.mul Id.refl p = Id.refl :=
--@Id.map (Group.S ZΩ.1.zero).carrier ZΩ.carrier _ _ (λ e, e.1 Id.refl) (power.one p)

end GroundZero.Algebra