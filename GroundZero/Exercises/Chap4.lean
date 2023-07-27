import GroundZero.Theorems.Functions
import GroundZero.Theorems.Equiv
import GroundZero.Types.Product
import GroundZero.Theorems.Nat
import GroundZero.Types.Sigma

import GroundZero.Exercises.Chap2

open GroundZero.Types
open GroundZero.Proto
open GroundZero

universe u v w k u' v' w' k'

-- exercise 4.3

namespace «4.3»
  open GroundZero.Types.Equiv (transport ideqv idtoeqv)
  open GroundZero.Theorems.Functions
  open GroundZero.Types.Id

  variable {A : Type u} {B : Type v} (f : A → B)

  hott lemma embdOfIshae (e : Ishae f) : isEmbedding f :=
  begin
    intro x y; fapply Qinv.toBiinv; fapply Sigma.mk;
    { intro p; exact (e.2.1 x)⁻¹ ⬝ ap e.1 p ⬝ (e.2.1 y) }; apply Prod.mk;
    { intro p; transitivity; apply Equiv.mapFunctoriality;
      transitivity; apply ap (· ⬝ _); apply Equiv.mapFunctoriality;
      transitivity; apply Equiv.bimap (λ p q, p ⬝ _ ⬝ q);
      apply Id.mapInv; symmetry; apply Id.invInv;
      symmetry; transitivity; symmetry; apply Equiv.idmap;
      transitivity; apply @Equiv.mapWithHomotopy B B idfun (f ∘ e.1) (λ x, (e.2.2.1 x)⁻¹);
      transitivity; apply Equiv.bimap (λ p q, p ⬝ _ ⬝ q);
      apply ap; symmetry; apply e.2.2.2;
      apply ap (·⁻¹⁻¹); symmetry; apply e.2.2.2;
      apply ap (_ ⬝ · ⬝ _); apply Equiv.mapOverComp };
    { intro p; induction p; transitivity; apply ap (· ⬝ _);
      apply Id.reflRight; apply Id.invComp }
  end

  hott lemma embdOfQinv : Qinv f → isEmbedding f :=
  embdOfIshae f ∘ Theorems.Equiv.qinvImplsIshae f

  hott corollary qinvIdEqv (e : Qinv f) {a b : A} : (a = b) ≃ (f a = f b) :=
  ⟨ap f, embdOfQinv f e a b⟩

  hott corollary qinvEqvLeft (e : Qinv f) {C : Type w} (g h : C → A) : (g ~ h) ≃ (f ∘ g ~ f ∘ h) :=
  begin apply Structures.equivFunext; intro; apply qinvIdEqv f e end

  hott theorem «4.1.1» (e : Qinv f) : Qinv f ≃ (Π (x : A), x = x) :=
  begin
    apply Equiv.trans; apply Sigma.respectsEquiv;
    intro g; apply Equiv.trans; apply Equiv.prodEquiv;

    apply Equiv.trans; apply qinvEqvLeft e.1 ⟨f, ⟨e.2.2, e.2.1⟩⟩;
    apply Equiv.trans; apply transport (· ∘ g ~ _ ≃ _) (Theorems.funext e.2.2)⁻¹;
    apply ideqv; apply Equiv.trans; symmetry; apply Theorems.full;
    apply Equiv.inveqv; apply ideqv;
    symmetry; apply Sigma.const; apply Equiv.trans;
    apply sigma.assoc (B → A) (λ g, e.1 = g) (λ w, w.1 ∘ f ~ idfun);
    apply Equiv.trans; apply Theorems.Equiv.contrFamily; apply singl.contr;

    apply Structures.equivFunext; intro x;
    apply Equiv.trans; apply qinvIdEqv f e;
    apply transport (· = _ ≃ _); symmetry; apply e.2.1;
    apply Equiv.symm; apply qinvIdEqv f e
  end
end «4.3»

-- exercise 4.4

namespace «4.4»
  open GroundZero.Types.Equiv (apd transport biinv ideqv)
  open GroundZero.Theorems.Functions
  open GroundZero.Types.Id

  hott lemma bisigmaComm (A : Type u) (B : Type v) (C : A → B → Type w) : (Σ x y, C x y) ≃ (Σ y x, C x y) :=
  ⟨λ w, ⟨w.2.1, w.1, w.2.2⟩, Qinv.toBiinv _ ⟨λ w, ⟨w.2.1, w.1, w.2.2⟩, (idp, idp)⟩⟩

  hott def mapProd {A : Type u} {A' : Type u'} {B : A → Type v} {B' : A' → Type v'}
    (f : A → A') (g : Π x, B x → B' (f x)) : (Σ x, B x) → (Σ y, B' y) :=
  λ w, ⟨f w.1, g w.1 w.2⟩

  hott lemma transportEmbd {A : Type u} {B : A → Type v} {a b : A} (p : a = b) : isEmbedding (transport B p) :=
  begin
    induction p; intro x y; apply transport biinv;
    show idfun = _; apply Theorems.funext; intro q;
    induction q; reflexivity; exact (ideqv (x = y)).2
  end

  hott corollary transportEmbdEqv {A : Type u} {B : A → Type v} {a b : A}
    (p : a = b) {x y : B a} : (x = y) ≃ (transport B p x = transport B p y) :=
  ⟨ap (transport B p), transportEmbd p x y⟩

  hott lemma mapProdFiber {A : Type u} {A' : Type u'} {B : A → Type v} {B' : A' → Type v'}
    (f : A → A') (g : Π x, B x → B' (f x)) (w' : Σ y, B' y) :
    fib (mapProd f g) w' ≃ Σ (e : fib f w'.1), fib (g e.1) (transport B' e.2⁻¹ w'.2) :=
  begin
    transitivity; apply Sigma.respectsEquiv.{_, _, max u' v'}; intro; apply Sigma.sigmaPath;
    transitivity; symmetry; apply sigma.assoc;
    transitivity; apply Sigma.respectsEquiv.{_, _, max v u' v'}; intro x;
    apply bisigmaComm (B x) (f x = w'.1) (λ y p, transport B' p (g x y) = w'.2);
    transitivity; apply sigma.assoc A (λ x, f x = w'.1) (λ e, Σ (y : B e.1), transport B' e.2 (g e.1 y) = w'.2);
    apply Sigma.respectsEquiv; intro e; apply Sigma.respectsEquiv; intro;
    transitivity; apply transportEmbdEqv e.2⁻¹; apply transport (· = _ ≃ _ = _);
    symmetry; apply Equiv.transportForwardAndBack; reflexivity
  end

  variable {A : Type u} {B : Type v} {C : Type w} (f : A → B) (g : B → C) (b : B)

  hott def naturalMap : fib (g ∘ f) (g b) → fib g (g b) :=
  λ w, ⟨f w.1, w.2⟩

  hott theorem «4.4.i» : fib (naturalMap f g b) ⟨b, idp (g b)⟩ ≃ fib f b :=
  begin
    apply Equiv.trans; apply @mapProdFiber A B (λ x, g (f x) = g b) (λ y, g y = g b) f (λ _, idfun) ⟨b, idp (g b)⟩;
    apply transport (@Sigma _ · ≃ _); apply Theorems.funext;
    intro e; symmetry; apply ap (fib idfun);
    transitivity; apply Equiv.transportOverContrMap;
    transitivity; apply Id.reflRight; apply ap (ap g); apply Id.invInv;
    apply Equiv.trans; apply Sigma.respectsEquiv;
    { intro; apply Equiv.trans; apply Sigma.hmtpyInvEqv;
      apply Structures.contrEquivUnit.{_, 0}; apply singl.contr };
    apply Equiv.trans; apply Sigma.const; apply Structures.unitProdEquiv;
  end

  hott theorem «4.4.ii» (c : C) : fib (g ∘ f) c ≃ Σ (w : fib g c), fib f w.1 :=
  begin
    apply Equiv.symm; apply Equiv.trans;
    apply sigma.assoc (fib g c) (λ _, A) (λ w, f w.2 = w.1.1);
    apply Equiv.trans; fapply Theorems.Equiv.respectsEquivOverFst;

    exact (Σ (a : A) (b : B), g b = c);
    { fapply Sigma.mk;
      { intro w; existsi w.2; existsi w.1.1; exact w.1.2 };
      apply Qinv.toBiinv; fapply Sigma.mk;
      { intro w; existsi ⟨w.2.1, w.2.2⟩; exact w.1 };
      apply Prod.mk <;> intro <;> reflexivity };

    apply Equiv.trans; symmetry; apply sigma.assoc;
    apply Sigma.respectsEquiv; intro a;
    apply Equiv.trans; symmetry; apply sigma.assoc;
    apply Equiv.trans; apply Sigma.respectsEquiv;
    intro b; apply Sigma.const (g b = c) (f a = b);

    fapply Sigma.mk; intro w; exact ap g w.2.2 ⬝ w.2.1; apply Qinv.toBiinv; fapply Sigma.mk;
    { intro p; existsi f a; existsi p; reflexivity }; apply Prod.mk; intro; reflexivity;
    { intro w; fapply Sigma.prod; exact w.2.2; transitivity;
      apply Equiv.transportOverProduct; apply Equiv.bimap Prod.mk;
      { transitivity; apply Equiv.transportOverContrMap; transitivity;
        apply ap (· ⬝ _); apply Id.mapInv; apply Id.invCompCancel };
      { transitivity; apply Equiv.transportOverInvContrMap; apply Equiv.idmap } }
  end
end «4.4»

-- exercise 4.6

namespace «4.6»
  open GroundZero.Types.Equiv (transport ideqv)

  hott def idtoqinv {A B : Type u} : A = B → Σ (f : A → B), Qinv f :=
  λ p, transport (λ X, Σ (f : A → X), Qinv f) p ⟨idfun, ⟨idfun, (idp, idp)⟩⟩

  variable (qinvua : Π (A B : Type u), Qinv (@idtoqinv A B))

  -- 4.6.i

  hott lemma lem1 {A B X : Type u} (p : A = B) : (X → A) ≃ (X → B) :=
  transport (λ Y, (X → A) ≃ (X → Y)) p (ideqv (X → A))

  hott lemma lem2 {A B X : Type u} (e : A ≃ B) : (X → A) ≃ (X → B) :=
  lem1 ((qinvua A B).1 ⟨e.1, Qinv.ofBiinv _ e.2⟩)

  -- then proceed exactly as in book

  -- 4.6.ii

  -- 4.6.iii
end «4.6»

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

-- exercise 4.9

example {A : Type u} {B : A → Type v} {f g : Π x, B x} : (f = g) ≃ (f ~ g) :=
Theorems.full -- see “Structures.lean” for this kind of proof
