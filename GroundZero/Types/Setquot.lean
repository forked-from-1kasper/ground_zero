import GroundZero.Types.Ens
open GroundZero.Structures

namespace GroundZero
universe u v w

namespace Types

hott def iseqclass {A : Type u} (R : eqrel A) (φ : Ens A) :=
φ.inh × (Π x y, R.apply x y → x ∈ φ → y ∈ φ) × (Π x y, x ∈ φ → y ∈ φ → R.apply x y)

hott def iseqclass.prop {A : Type u} {R : eqrel A} (φ : Ens A) : prop (iseqclass R φ) :=
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

hott def setquot {A : Type u} (R : eqrel A) :=
Σ (φ : Ens A), iseqclass R φ

noncomputable hott def setquot.set {A : Type u} (R : eqrel A) : hset (setquot R) :=
begin
  fapply hsetRespectsSigma; apply Ens.isset;
  intro; apply propIsSet; apply iseqclass.prop
end

hott def setquot.elem {A : Type u} {R : eqrel A} (x : A) : setquot R :=
⟨⟨λ y, R.apply x y, R.prop x⟩,
  (HITs.Merely.elem ⟨x, R.refl x⟩,
   λ _ _ p q, R.trans q p,
   λ _ _ p q, R.trans (R.symm p) q)⟩

noncomputable hott def setquot.sound {A : Type u} {R : eqrel A} {x y : A} :
  R.apply x y → @setquot.elem A R x = setquot.elem y :=
begin
  intro p; fapply Types.Sigma.prod;
  { apply Ens.ext; intro z; apply Prod.mk <;> intro q;
    { apply R.trans; exact R.symm p; exact q };
    { apply R.trans; exact p; exact q } };
  { apply iseqclass.prop }
end

end Types

end GroundZero