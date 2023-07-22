import GroundZero.Theorems.Equiv
import GroundZero.Theorems.Nat
import GroundZero.Types.Lost

open GroundZero GroundZero.Types
open GroundZero.Types.Equiv
open GroundZero.Theorems
open GroundZero.Proto

open GroundZero.Structures (dec prop contr propset)

universe u v

-- exercise 3.9

hott def lemTrue {A : Type u} (H : prop A) (lem : LEM₋₁) (x : A) : lem A H = Sum.inl x :=
begin
  match lem A H with | Sum.inl y => _ | Sum.inr φ => _;
  apply Id.map; apply H; apply Empty.elim; apply φ x
end

hott def lemFalse {A : Type u} (H : prop A) (lem : LEM₋₁) (φ : ¬A) : lem A H = Sum.inr φ :=
begin
  match lem A H with | Sum.inl x => _ | Sum.inr ψ => _;
  apply Empty.elim; apply φ x; apply Id.map; apply Structures.notIsProp
end

hott lemma propsetInhIsProp (A : propset) : prop A.1 := A.2

hott theorem lemImplPropEqvBool : LEMprop.{u} → propset.{u} ≃ 𝟐 :=
begin
  intro lem; fapply Sigma.mk;
  { intro w; exact Coproduct.elim (λ _, true) (λ _, false) (lem w.1 w.2) };

  apply Qinv.toBiinv; fapply Sigma.mk;
  { fapply Bool.elim; exact ⟨𝟎, Structures.emptyIsProp⟩; exact ⟨𝟏, Structures.unitIsProp⟩ }; apply Prod.mk;

  { intro b; induction b using Bool.casesOn;
    { transitivity; apply Id.map (Coproduct.elim _ _); apply lemFalse; apply Empty.elim; reflexivity };
    { transitivity; apply Id.map (Coproduct.elim _ _); apply lemTrue; exact ★; reflexivity } };

  { intro w; apply Sigma.prod; apply Structures.propIsProp;
    match lem w.1 w.2 with | Sum.inl x => _ | Sum.inr φ => _;

    transitivity; apply Id.map; apply Id.map (Bool.elim _ _); apply Id.map (Coproduct.elim _ _);
    apply lemTrue; exact x; symmetry; apply ua; apply Structures.contrEquivUnit;
    fapply Sigma.mk; exact x; intro y; apply w.2;

    transitivity; apply Id.map; apply Id.map (Bool.elim _ _); apply Id.map (Coproduct.elim _ _);
    apply lemFalse; exact φ; symmetry; apply ua; apply uninhabitedType; exact Empty.elim ∘ φ }
end

-- exercise 3.19

namespace «3.19»
  variable {P : ℕ → Type u} (H : Π n, prop (P n)) (G : Π n, dec (P n))
end «3.19»
