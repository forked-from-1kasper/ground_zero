import GroundZero.Theorems.Equiv
import GroundZero.Theorems.Nat
import GroundZero.Types.Lost

open GroundZero GroundZero.Types
open GroundZero.Types.Equiv
open GroundZero.Theorems
open GroundZero.Proto

open GroundZero.Structures (dec prop contr propset)
open GroundZero.Types.Id (ap)

universe u v

-- exercise 3.9

namespace «3.9»
  hott def lemTrue {A : Type u} {H : prop A} {lem : LEM₋₁} (x : A) : lem A H = Sum.inl x :=
  begin
    match lem A H with | Sum.inl y => _ | Sum.inr φ => _;
    { apply Id.map; apply H }; { apply Empty.elim; apply φ x }
  end

  hott def lemFalse {A : Type u} {H : prop A} {lem : LEM₋₁} (φ : ¬A) : lem A H = Sum.inr φ :=
  begin
    match lem A H with | Sum.inl x => _ | Sum.inr ψ => _;
    { apply Empty.elim; apply φ x };
    { apply Id.ap; apply Structures.notIsProp }
  end

  hott def Ωelim (lem : LEMprop.{u}) : propset.{u} → 𝟐 :=
  λ w, Coproduct.elim (λ _, true) (λ _, false) (lem w.1 w.2)

  hott def Ωintro : 𝟐 → propset :=
  Bool.elim ⟨𝟎, Structures.emptyIsProp⟩ ⟨𝟏, Structures.unitIsProp⟩

  hott lemma propsetInhIsProp (A : propset) : prop A.1 := A.2

  hott lemma Ωlinv (lem : LEMprop.{u}) : Ωelim lem ∘ Ωintro ~ idfun
  | false => ap (Coproduct.elim _ _) (lemFalse Empty.elim)
  | true  => ap (Coproduct.elim _ _) (lemTrue ★)

  hott lemma Ωrinv (lem : LEMprop.{u}) : Ωintro ∘ Ωelim lem ~ idfun :=
  begin
    intro w; apply Equiv.propset.Id; match lem w.1 w.2 with | Sum.inl x => _ | Sum.inr φ => _;

    transitivity; apply Id.map; apply Id.map (Bool.elim _ _); apply Id.map (Coproduct.elim _ _);
    apply lemTrue; exact x; symmetry; apply ua; apply Structures.contrEquivUnit;
    fapply Sigma.mk; exact x; intro y; apply w.2;

    transitivity; apply Id.map; apply Id.map (Bool.elim _ _); apply Id.map (Coproduct.elim _ _);
    apply lemFalse; exact φ; symmetry; apply ua; apply uninhabitedType; exact Empty.elim ∘ φ
  end

  hott theorem lemImplPropEqvBool (lem : LEMprop.{u}) : propset.{u} ≃ 𝟐 :=
  ⟨Ωelim lem, Qinv.toBiinv _ ⟨Ωintro, (Ωlinv lem, Ωrinv lem)⟩⟩
end «3.9»

-- exercise 3.10

namespace «3.10»
  open «3.9»

  inductive Resize (A : Type u) : Type (max u v)
  | intro : A → Resize A

  hott def Resize.elim {A : Type u} : Resize A → A
  | intro w => w

  hott theorem Resize.equiv (A : Type u) : A ≃ Resize.{u, v} A :=
  ⟨Resize.intro, Qinv.toBiinv _ ⟨Resize.elim, (λ (Resize.intro _), idp _, idp)⟩⟩

  hott lemma Resize.prop {A : Type u} (H : prop A) : prop (Resize.{u, v} A) :=
  Structures.propRespectsEquiv.{u, max u v} (Resize.equiv A) H

  hott def ResizeΩ : propset.{u} → propset.{max u v} :=
  λ w, ⟨Resize.{u, v} w.1, Resize.prop w.2⟩

  hott lemma lemCumulativity (lem : LEMprop.{max u v}) : LEMprop.{u} :=
  λ A H, match lem (Resize.{u, v} A) (Resize.prop H) with
  | Sum.inl x => Sum.inl (Resize.elim x)
  | Sum.inr φ => Sum.inr (φ ∘ Resize.intro)

  hott corollary lemSucCumulativity : LEMprop.{u + 1} → LEMprop.{u} :=
  lemCumulativity.{u, u + 1}

  hott lemma lemImplPropUniverseEqv (lem : LEMprop.{max u v}) : propset.{u} ≃ propset.{max u v} :=
  Equiv.trans (lemImplPropEqvBool (lemCumulativity.{u, v} lem))
              (Equiv.symm (lemImplPropEqvBool lem))

  hott lemma resizeUniqLem1 (lem : LEMprop.{max u v}) : (lemImplPropUniverseEqv.{u, v} lem).1 ∘ Ωintro ~ ResizeΩ.{u, v} ∘ Ωintro :=
  begin
    intro b; transitivity; apply ap Ωintro; apply Ωlinv; apply Equiv.propset.Id;
    symmetry; apply ua; induction b using Bool.casesOn;
    { apply uninhabitedType; exact Empty.elim ∘ Resize.elim };
    { apply Structures.contrEquivUnit; existsi Resize.intro ★;
      intro (Resize.intro b); apply ap; apply Structures.unitIsProp }
  end

  hott lemma resizeUniqLem2 (lem : LEMprop.{max u v}) : (lemImplPropUniverseEqv.{u, v} lem).1 ~ ResizeΩ.{u, v} :=
  begin
    intro w; transitivity; apply ap; symmetry; apply Ωrinv (lemCumulativity.{u, v} lem);
    transitivity; apply resizeUniqLem1; apply ap ResizeΩ; apply Ωrinv
  end

  hott theorem lemImplResizing (lem : LEMprop.{max u v}) : biinv ResizeΩ :=
  transport biinv (Theorems.funext (resizeUniqLem2.{u, v} lem)) (lemImplPropUniverseEqv lem).2
end «3.10»

-- exercise 3.19

namespace «3.19»
  variable {P : ℕ → Type u} (H : Π n, prop (P n)) (G : Π n, dec (P n))
end «3.19»
