import GroundZero.Theorems.Equiv
import GroundZero.Theorems.Nat
import GroundZero.Types.Lost

open GroundZero GroundZero.Types
open GroundZero.Types.Equiv
open GroundZero.Theorems
open GroundZero.Proto

open GroundZero.Structures (dec prop contr)
open GroundZero.Types.Id (ap)

universe u v w

-- exercise 3.9

namespace «3.9»
  section
    variable {A : Type u} {H : prop A} {lem : LEM₋₁}

    hott def lemTrue (x : A) : lem A H = Sum.inl x :=
    match lem A H with
    | Sum.inl y => ap Sum.inl (H y x)
    | Sum.inr φ => Empty.elim (φ x)

    hott def lemFalse (φ : ¬A) : lem A H = Sum.inr φ :=
    match lem A H with
    | Sum.inl x => Empty.elim (φ x)
    | Sum.inr ψ => ap Sum.inr (Structures.notIsProp ψ φ)
  end

  hott def Ωelim (lem : LEM₋₁ u) : Prop u → 𝟐 :=
  λ w, Coproduct.elim (λ _, true) (λ _, false) (lem w.1 w.2)

  hott def Ωintro : 𝟐 → Prop :=
  Bool.elim ⟨𝟎, Structures.emptyIsProp⟩ ⟨𝟏, Structures.unitIsProp⟩

  hott lemma propsetInhIsProp (A : Prop) : prop A.1 := A.2

  hott lemma Ωlinv (lem : LEM₋₁) : Ωelim lem ∘ Ωintro ~ idfun
  | false => ap (Coproduct.elim _ _) (lemFalse Empty.elim)
  | true  => ap (Coproduct.elim _ _) (lemTrue ★)

  hott lemma Ωrinv (lem : LEM₋₁) : Ωintro ∘ Ωelim lem ~ idfun :=
  begin
    intro w; apply Equiv.propset.Id; match lem w.1 w.2 with | Sum.inl x => _ | Sum.inr φ => _;

    transitivity; apply Id.map; apply Id.map (Bool.elim _ _); apply Id.map (Coproduct.elim _ _);
    apply lemTrue x; symmetry; apply ua; apply Structures.contrEquivUnit;
    fapply Sigma.mk; exact x; intro y; apply w.2;

    transitivity; apply Id.map; apply Id.map (Bool.elim _ _); apply Id.map (Coproduct.elim _ _);
    apply lemFalse φ; symmetry; apply ua; apply uninhabitedType; exact Empty.elim ∘ φ
  end

  hott theorem lemImplPropEqvBool (lem : LEM₋₁) : Prop u ≃ 𝟐 :=
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

  hott def ResizeΩ : Prop u → Prop (max u v) :=
  λ w, ⟨Resize.{u, v} w.1, Resize.prop w.2⟩

  hott lemma lemCumulativity (lem : LEM₋₁ (max u v)) : LEM₋₁ u :=
  λ A H, match lem (Resize.{u, v} A) (Resize.prop H) with
  | Sum.inl x => Sum.inl (Resize.elim x)
  | Sum.inr φ => Sum.inr (φ ∘ Resize.intro)

  hott corollary lemSucCumulativity : LEM₋₁ (u + 1) → LEM₋₁ u :=
  lemCumulativity.{u, u + 1}

  hott lemma lemImplPropUniverseEqv (lem : LEM₋₁ (max u v)) : Prop u ≃ Prop (max u v) :=
  Equiv.trans (lemImplPropEqvBool (lemCumulativity.{u, v} lem))
              (Equiv.symm (lemImplPropEqvBool lem))

  hott lemma resizeUniqLem1 (lem : LEM₋₁ (max u v)) : (lemImplPropUniverseEqv.{u, v} lem).1 ∘ Ωintro ~ ResizeΩ.{u, v} ∘ Ωintro :=
  begin
    intro b; transitivity; apply ap Ωintro; apply Ωlinv; apply Equiv.propset.Id;
    symmetry; apply ua; induction b using Bool.casesOn;
    { apply uninhabitedType; exact Empty.elim ∘ Resize.elim };
    { apply Structures.contrEquivUnit; existsi Resize.intro ★;
      intro (Resize.intro b); apply ap; apply Structures.unitIsProp }
  end

  hott lemma resizeUniqLem2 (lem : LEM₋₁ (max u v)) : (lemImplPropUniverseEqv.{u, v} lem).1 ~ ResizeΩ.{u, v} :=
  begin
    intro w; transitivity; apply ap; symmetry; apply Ωrinv (lemCumulativity.{u, v} lem);
    transitivity; apply resizeUniqLem1; apply ap ResizeΩ; apply Ωrinv
  end

  hott theorem lemImplResizing (lem : LEM₋₁ (max u v)) : biinv ResizeΩ :=
  transport biinv (Theorems.funext (resizeUniqLem2.{u, v} lem)) (lemImplPropUniverseEqv lem).2

  hott corollary lemImplResizingSuc : LEM₋₁ (u + 1) → biinv ResizeΩ.{u, u + 1} :=
  lemImplResizing.{u, u + 1}
end «3.10»

-- exercise 3.11

namespace «3.11»
  open HITs.Interval (happly)
  open ua (negBoolEquiv)
  open HITs

  hott lemma negBoolNoFixPoint : Π (x : 𝟐), not x ≠ x
  | false => λ p, Structures.ffNeqTt p⁻¹
  | true  => λ p, Structures.ffNeqTt p

  hott theorem WCInfDisproved : ¬(Π (A : Type), ∥A∥ → A) :=
  begin
    intro f;
    let p := ua negBoolEquiv;

    let α := λ u, ua.transportRule negBoolEquiv (f 𝟐 u);
    let β := λ u, ap (λ w, transport (λ A, A) p (f 𝟐 w))
                     (Merely.uniq u (transport (λ A, ∥A∥) p⁻¹ u));
    let γ := (transportOverFunctor (λ A, ∥A∥) (λ A, A) (f 𝟐) p)⁻¹ ⬝ apd f p;
    let e := λ u, (α u)⁻¹ ⬝ β u ⬝ happly γ u;
  
    apply negBoolNoFixPoint; exact e (Merely.elem false)
  end

  hott lemma merelyImplDneg {A : Type u} : ∥A∥ → ¬¬A :=
  HITs.Merely.rec Structures.notIsProp (λ x φ, φ x)

  -- Theorem 3.2.2
  hott corollary dnegInfDisproved : ¬(Π (A : Type), (¬¬A) → A) :=
  λ H, WCInfDisproved (λ A, H A ∘ merelyImplDneg)
end «3.11»

-- exercise 3.12

namespace «3.12»
  hott lemma implOfSum {A : Type u} {B : Type v} : (¬A) + B → A → B
  | Sum.inl φ => λ a, Empty.elim (φ a)
  | Sum.inr b => λ _, b

  hott theorem WC (lem : LEM₋₁ u) : Π (A : Type u), ∥(∥A∥ → A)∥ :=
  begin
    intro A; apply HITs.Merely.lift; apply implOfSum;
    match lem ∥A∥ HITs.Merely.uniq with | Sum.inl x => _ | Sum.inr φ => _;
    apply HITs.Merely.lift; apply Sum.inr; assumption;
    apply HITs.Merely.elem; left; assumption
  end
end «3.12»

-- exercise 3.13

namespace «3.13»
  open Structures (hset)
  open «3.11»

  hott lemma LEMinfDual (lem : LEM∞ v) {A : Type u} {B : A → Type v} : ¬(Σ x, ¬B x) → Π x, B x :=
  λ φ x, match lem (B x) with
  | Sum.inl b => b
  | Sum.inr ψ => Empty.elim (φ ⟨x, ψ⟩)

  hott lemma LEMinfImplDNegInf (lem : LEM∞ u) {A : Type u} : ∥A∥ → A :=
  match lem A with
  | Sum.inl a => λ _, a
  | Sum.inr φ => λ w, Empty.elim (@merelyImplDneg A w φ)

  -- see lemma 3.8.2
  hott theorem LEMinfImplCartesian (lem : LEM∞ v) (A : Type u) (B : A → Type v) :
    hset A → (Π x, hset (B x)) → (Π x, ∥B x∥) → ∥Π x, B x∥ :=
  λ _ _ f, HITs.Merely.elem (λ x, LEMinfImplDNegInf lem (f x))

  hott theorem LEMinfImplAC (lem : LEM∞ (max v w)) {A : Type u} (B : A → Type v) (η : Π x, B x → Type w) :
    hset A → (Π x, hset (B x)) → (Π x y, prop (η x y)) →
    (Π (x : A), ∥(Σ (y : B x), η x y)∥) →
    ∥(Σ (φ : Π x, B x), Π x, η x (φ x))∥ :=
  λ _ _ _ f, HITs.Merely.elem ⟨λ x, (LEMinfImplDNegInf lem (f x)).1,
                               λ x, (LEMinfImplDNegInf lem (f x)).2⟩
end «3.13»

-- exercise 3.19

namespace «3.19»
  variable {P : ℕ → Type u} (H : Π n, prop (P n)) (G : Π n, dec (P n))
end «3.19»
