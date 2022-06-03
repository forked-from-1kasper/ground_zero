import GroundZero.Types.Ens
open GroundZero.Structures

namespace GroundZero
universe u v w

namespace Types

hott def iseqclass {α : Type u} (R : eqrel α) (φ : Ens α) :=
φ.inh × (Π x y, R.apply x y → x ∈ φ → y ∈ φ) × (Π x y, x ∈ φ → y ∈ φ → R.apply x y)

hott def iseqclass.prop {α : Type u} {R : eqrel α} (φ : Ens α) : prop (iseqclass R φ) :=
begin
  apply productProp; apply HITs.Merely.uniq;
  apply productProp;

  -- TODO: fix this boilerplate
  apply piProp; intro;
  apply piProp; intro;
  apply piProp; intro;
  apply piProp; intro;
  apply Ens.prop;
  
  apply piProp; intro;
  apply piProp; intro;
  apply piProp; intro;
  apply piProp; intro;
  apply R.prop
end

hott def setquot {α : Type u} (R : eqrel α) :=
Σ (φ : Ens α), iseqclass R φ

noncomputable hott def setquot.set {α : Type u} (R : eqrel α) : hset (setquot R) :=
begin
  fapply hsetRespectsSigma; apply Ens.isset;
  intro; apply propIsSet; apply iseqclass.prop
end

hott def setquot.elem {α : Type u} {R : eqrel α} (x : α) : setquot R :=
⟨⟨λ y, R.apply x y, R.prop x⟩,
  (HITs.Merely.elem ⟨x, R.refl x⟩,
   λ a b p q, R.trans q p,
   λ a b p q, R.trans (R.symm p) q)⟩

noncomputable hott def setquot.sound {α : Type u} {R : eqrel α} {x y : α} :
  R.apply x y → @setquot.elem α R x = setquot.elem y :=
begin
  intro p; fapply Types.Sigma.prod;
  { apply Ens.ext; intro z; apply Prod.mk <;> intro q;
    { apply R.trans; exact R.symm p; exact q };
    { apply R.trans; exact p; exact q } };
  { apply iseqclass.prop }
end

end Types

end GroundZero