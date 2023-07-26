import GroundZero.Theorems.Functions
import GroundZero.Theorems.Equiv
import GroundZero.Types.Product
import GroundZero.Theorems.Nat
import GroundZero.Types.Sigma

open GroundZero.Types
open GroundZero.Proto
open GroundZero

universe u v w k

-- exercise 4.7

namespace «4.7»
  open GroundZero.Types.Equiv (biinv transport)
  open GroundZero.Theorems.Functions
  open GroundZero.Types.Id

  hott theorem embdEqvDef {A : Type u} {B : Type v} (f : A → B) :
    isEmbedding f ↔ injective f × Π x, biinv (@ap A B x x f) :=
  begin
    apply Prod.mk;
    { intro e; apply Prod.mk;
      { intro x y; exact (e x y).2.1 };
      { intro x; exact e x x } };
    { intro w x y; fapply Qinv.toBiinv; let ε := λ x, Qinv.ofBiinv _ (w.2 x);
      fapply Sigma.mk;
      { intro p; exact transport (λ y, f x = f y → x = y) (w.1 x y p) (ε x).1 p }; apply Prod.mk;
      { intro p; transitivity; apply ap (ap f); transitivity;
        apply HITs.Interval.happly; apply Equiv.transportCharacterization;
        apply Equiv.transportComposition; transitivity;
        apply ap (λ q, ap f ((ε x).1 q ⬝ _));
        apply Equiv.transportOverInvContrMap;
        transitivity; apply Equiv.mapFunctoriality;
        transitivity; apply ap (· ⬝ _); apply (ε x).2.1;
        transitivity; apply ap (_ ⬝ · ⬝ _); apply Id.mapInv;
        apply Id.cancelInvComp };
      { intro p; show transport (λ y, f x = f y → x = y) _ _ _ = _;
        transitivity; apply HITs.Interval.happly; apply Equiv.transportCharacterization;
        transitivity; apply Equiv.transportComposition;
        transitivity; apply ap (· ⬝ _);
        transitivity; apply ap (ε x).1;
        transitivity; apply Equiv.transportOverInvContrMap;
        symmetry; apply Equiv.mapFunctoriality;
        apply (ε x).2.2; apply Id.cancelInvComp } }
  end
end «4.7»

-- exercise 4.8

namespace «4.8»
  open GroundZero.Theorems.Functions
  open GroundZero.Types.Equiv
  open GroundZero.Structures
  open GroundZero.Theorems

  hott theorem injOutOfBoolChar {B : Type u} : (Σ (f : 𝟐 → B), injective f) ≃ (Σ (w : B × B), w.1 ≠ w.2) :=
  begin
    fapply Sigma.mk;
    { intro w; existsi (w.1 false, w.1 true);
      intro p; apply ffNeqTt; apply w.2; exact p };
    fapply Qinv.toBiinv; fapply Sigma.mk;
    { intro w; existsi Bool.elim w.1.1 w.1.2;
      intro b₁ b₂ p; match b₁, b₂ with
      | false, false => { reflexivity }
      | false, true  => { apply Empty.elim; apply w.2; exact p }
      | true,  false => { apply Empty.elim; apply w.2; exact p⁻¹ }
      | true,  true  => { reflexivity } };
    apply Prod.mk;
    { intro w; apply Sigma.prod; apply notIsProp; reflexivity };
    { intro b; apply Sigma.prod;
      { repeat (first | apply boolIsSet | apply piProp; intro) };
      { apply Theorems.funext; intro b; induction b using Bool.casesOn <;> reflexivity } }
  end

  hott theorem embdOutOfBoolChar {B : Type u} :
    (𝟐 ↪ B) ≃ (Σ (w : B × B), w.1 ≠ w.2 × contr (w.1 = w.1) × contr (w.2 = w.2)) :=
  begin
    fapply Sigma.mk;
    { intro w; existsi (w.1 false, w.1 true); fapply (_, _, _);
      { intro p; apply ffNeqTt; apply (w.2 false true).1.1; exact p };
      { apply contrRespectsEquiv; apply w.eqv;
        existsi idp false; intro; apply boolIsSet };
      { apply contrRespectsEquiv; apply w.eqv;
        existsi idp true; intro; apply boolIsSet } };
    fapply Qinv.toBiinv; fapply Sigma.mk;
    { intro w; existsi Bool.elim w.1.1 w.1.2; intro b₁ b₂; apply Qinv.toBiinv;
      match b₁, b₂ with
      | false, false => { fapply Sigma.mk; intro; reflexivity; apply Prod.mk;
                          { intro; apply contrImplProp; apply w.2.2.1 };
                          { intro; apply boolIsSet } }
      | false, true  => { fapply Sigma.mk; intro p; apply Empty.elim; apply w.2.1 p; apply Prod.mk;
                          { intro p; apply Empty.elim; apply w.2.1 p };
                          { intro; apply Empty.elim; apply ffNeqTt; assumption } }
      | true,  false => { fapply Sigma.mk; intro p; apply Empty.elim; apply w.2.1 p⁻¹; apply Prod.mk;
                          { intro p; apply Empty.elim; apply w.2.1 p⁻¹ };
                          { intro; apply Empty.elim; apply ffNeqTt; symmetry; assumption } }
      | true,  true  => { fapply Sigma.mk; intro; reflexivity; apply Prod.mk;
                          { intro; apply contrImplProp; apply w.2.2.2 };
                          { intro; apply boolIsSet } } };
    apply Prod.mk;
    { intro w; apply Sigma.prod; apply productProp; apply notIsProp;
      apply productProp <;> apply contrIsProp; reflexivity };
    { intro b; apply Sigma.prod;
      { apply piProp; intro; apply piProp; intro; apply Equiv.biinvProp };
      { apply Theorems.funext; intro b; induction b using Bool.casesOn <;> reflexivity } }
  end
end «4.8»
