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

  hott lemma merelyImplDn {A : Type u} : ∥A∥ → ¬¬A :=
  HITs.Merely.rec Structures.notIsProp (λ x φ, φ x)

  -- Theorem 3.2.2
  hott corollary dnInfDisproved : ¬(Π (A : Type), (¬¬A) → A) :=
  λ H, WCInfDisproved (λ A, H A ∘ merelyImplDn)
end «3.11»

-- exercise 3.12

namespace «3.12»
  hott lemma implOfSum {A : Type u} {B : Type v} : (¬A) + B → A → B
  | Sum.inl φ => Empty.elim ∘ φ
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

  hott lemma LEMinfImplDNInf (lem : LEM∞ u) {A : Type u} : ∥A∥ → A :=
  match lem A with
  | Sum.inl a => λ _, a
  | Sum.inr φ => λ w, Empty.elim (@merelyImplDn A w φ)

  -- see lemma 3.8.2
  hott theorem LEMinfImplCartesian (lem : LEM∞ v) (A : Type u) (B : A → Type v) :
    hset A → (Π x, hset (B x)) → (Π x, ∥B x∥) → ∥Π x, B x∥ :=
  λ _ _ f, HITs.Merely.elem (λ x, LEMinfImplDNInf lem (f x))

  hott theorem LEMinfImplAC (lem : LEM∞ (max v w)) {A : Type u} (B : A → Type v) (η : Π x, B x → Type w) :
    hset A → (Π x, hset (B x)) →
             (Π x y, prop (η x y)) →
             (Π (x : A), ∥(Σ (y : B x), η x y)∥) →
            ∥(Σ (φ : Π x, B x), Π x, η x (φ x))∥ :=
  λ _ _ _ f, HITs.Merely.elem ⟨λ x, (LEMinfImplDNInf lem (f x)).1,
                               λ x, (LEMinfImplDNInf lem (f x)).2⟩

  hott lemma LEMinfDual (lem : LEM∞ v) {A : Type u} {B : A → Type v} : ¬(Σ x, ¬B x) → Π x, B x :=
  λ φ x, match lem (B x) with
  | Sum.inl b => b
  | Sum.inr ψ => Empty.elim (φ ⟨x, ψ⟩)
end «3.13»

-- exercise 3.14

namespace «3.14»
  open HITs.Interval (happly)
  open «3.11»
  open «3.9»

  hott def dn.intro {A : Type u} : A → ¬¬A :=
  λ x φ, φ x

  hott def dn.rec (lem : LEM₋₁ v) {A : Type u} {B : Type v} : prop B → (A → B) → (¬¬A → B) :=
  λ H f, Coproduct.elim (λ b _, b) (λ φ g, Empty.elim (g (φ ∘ f))) (lem B H)

  hott def dn.recβrule (lem : LEM₋₁ v) {A : Type u} {B : Type v} {H : prop B}
    {f : A → B} (x : A) : dn.rec lem H f (dn.intro x) = f x :=
  H _ _

  hott def dnImplMerely (lem : LEM₋₁ u) {A : Type u} : ¬¬A → ∥A∥ :=
  dn.rec lem HITs.Merely.uniq HITs.Merely.elem

  hott def lemMerelyEqvDef (lem : LEM₋₁ u) {A : Type u} : ¬¬A ≃ ∥A∥ :=
  Structures.propEquivLemma Structures.notIsProp HITs.Merely.uniq (dnImplMerely lem) merelyImplDn
end «3.14»

-- exercise 3.16

namespace «3.16.1»
  open GroundZero.Structures

  -- “hset X” isn’t useful here
  variable (X : Type u) (Y : X → Type v) (G : Π x, prop (Y x))

  hott lemma dn.elim : ¬¬(Π x, Y x) → (Π x, ¬¬(Y x)) :=
  λ φ x f, φ (λ g, f (g x))

  hott lemma dn.intro (lem : LEM₋₁ v) : (Π x, ¬¬(Y x)) → ¬¬(Π x, Y x) :=
  λ φ f, f (λ x, match lem (Y x) (G x) with
  | Sum.inl y => y
  | Sum.inr g => Empty.elim (φ x g))

  hott theorem dn.comm (lem : LEM₋₁ v) : ¬¬(Π x, Y x) ≃ (Π x, ¬¬(Y x)) :=
  begin
    apply propEquivLemma; apply notIsProp; apply piProp; intro; apply notIsProp;
    apply dn.elim; apply dn.intro <;> assumption
  end
end «3.16.1»

namespace «3.16.2»
  open GroundZero.Structures
  open GroundZero.HITs
  open «3.10»
  open «3.11»
  open «3.14»
  open «3.16.1»

  variable (X : Type u) (Y : X → Type v) (H : hset X) (G : Π x, hset (Y x)) (lem : LEM₋₁ (max u v))

  hott lemma elim (H : (Π x, ∥Y x∥) → ∥Π x, Y x∥) : (Π x, ¬¬(Y x)) → ¬¬(Π x, Y x) :=
  λ φ, merelyImplDn (H (λ x, dnImplMerely (lemCumulativity.{v, u} lem) (φ x)))

  hott lemma intro (H : (Π x, ¬¬(Y x)) → ¬¬(Π x, Y x)) : (Π x, ∥Y x∥) → ∥Π x, Y x∥ :=
  λ φ, dnImplMerely lem (H (λ x, merelyImplDn (φ x)))

  hott theorem DNComEqvAC : ((Π x, ¬¬(Y x)) ≃ ¬¬(Π x, Y x)) ≃ ((Π x, ∥Y x∥) → ∥Π x, Y x∥) :=
  begin
    transitivity; apply @propEquivLemma _ ((Π x, ¬¬(Y x)) → ¬¬(Π x, Y x));
    { apply Equiv.propEquivProp; apply notIsProp };
    { apply piProp; intro; apply notIsProp };
    { apply Equiv.forward };
    { intro φ; apply propEquivLemma;
      { apply piProp; intro; apply notIsProp };
      { apply notIsProp };
      { exact φ };
      { apply dn.elim } };
    { apply propEquivLemma;
      { apply piProp; intro; apply notIsProp };
      { apply piProp; intro; apply Merely.uniq };
      { apply intro; assumption };
      { apply elim; assumption } }
  end
end «3.16.2»

-- exercise 3.17

namespace «3.17»
  variable (Merely : Type u → Type u)
           (elem   : Π A, A → Merely A)
           (uniq   : Π A, prop (Merely A))
           (mrec   : Π A B, prop B → (A → B) → (Merely A → B))

  def mind {A : Type u} (B : Merely A → Type v) (H : Π x, prop (B x)) (f : Π x, B (elem A x)) : Π x, B x :=
  λ x, mrec A (B x) (H x) (λ y, transport B (uniq A (elem A y) x) (f y)) x
end «3.17»

-- exercise 3.18

namespace «3.18»
  open GroundZero.Structures

  hott theorem lemIffDneg : LEM₋₁ u ↔ DNEG₋₁ u :=
  begin
    apply Prod.mk; intro lem P H nnp;
    induction lem P H using Sum.casesOn;
    case inl p  => { exact p };
    case inr np => { apply Empty.elim (nnp np) };

    intro dneg P H; apply dneg; apply propEM H; intro npnp;
    apply npnp; right; intro p; apply npnp; left; exact p
  end

  hott corollary lemEqvDneg : LEM₋₁ u ≃ DNEG₋₁ u :=
  begin
    apply propIffLemma;
    { repeat (first | apply propEM; assumption | apply piProp; intro) };
    { repeat (first | assumption | apply piProp; intro) };
    { apply lemIffDneg }
  end
end «3.18»

-- exercise 3.19

namespace «3.19»
  variable {P : ℕ → Type u} (H : Π n, prop (P n)) (G : Π n, dec (P n))
  open GroundZero.HITs

  hott def BSA (n : ℕ) : ℕ → ℕ
  | Nat.zero   => n
  | Nat.succ m => Coproduct.elim (λ _, n) (λ _, BSA (Nat.succ n) m) (G n)

  hott def BS := BSA G Nat.zero

  hott lemma BSP (n m : ℕ) : P (n + m) → P (BSA G n m) :=
  begin
    intro h; induction m using Nat.casesOn;
    case zero   => { exact h };
    case succ m => { show P (Coproduct.elim _ _ _); induction G n using Sum.casesOn;
                     case inl p  => { exact p };
                     case inr np => { apply BSP (Nat.succ n) m;
                                      exact transport P (Nat.succPlus n m)⁻¹ h }; };
  end

  hott lemma minimality (n m k : ℕ) : P k → n ≤ k → BSA G n m ≤ k :=
  begin
    intro pk h; induction m using Nat.casesOn;
    case zero   => { exact h };
    case succ m => { show Coproduct.elim _ _ _ ≤ _; induction G n using Sum.casesOn;
                     case inl p  => { exact h };
                     case inr np => { apply minimality (Nat.succ n) m k pk;
                                      apply Nat.le.neqSucc;
                                      { intro ω; apply np; apply transport P;
                                        symmetry; apply ap Nat.pred ω; exact pk };
                                      apply Nat.le.map; exact h } }
  end

  hott lemma minExists : (Σ n, P n) → Σ n, P n × Π m, P m → n ≤ m :=
  λ w, ⟨BS G w.1, (BSP G Nat.zero w.1 (transport P (Nat.zeroPlus w.1)⁻¹ w.2),
                   λ m h, minimality G Nat.zero w.1 m h (Nat.max.zeroLeft m))⟩

  hott lemma minUnique : prop (Σ n, P n × Π m, P m → n ≤ m) :=
  λ w₁ w₂, Sigma.prod (Nat.le.asymm (w₁.2.2 w₂.1 w₂.2.1) (w₂.2.2 w₁.1 w₁.2.1))
                      (Structures.productProp (H _) (Structures.piProp
                        (λ _, Structures.piProp (λ _, Nat.le.prop _ _))) _ _)

  hott theorem elimMerelyDecPropFamily : ∥Σ n, P n∥ → Σ n, P n :=
  begin
    fapply Function.comp; exact (Σ n, P n × Π m, P m → n ≤ m);
    intro w; existsi w.1; exact w.2.1; apply Function.comp;
    apply Merely.rec; apply minUnique H; exact idfun;
    apply Merely.lift; apply minExists G
  end

  hott lemma upperEstimate (n m : ℕ) : BSA G n m ≤ n + m :=
  begin
    induction m using Nat.casesOn;
    case zero   => { apply Nat.max.refl };
    case succ m => { show Coproduct.elim _ _ _ ≤ _; induction G n using Sum.casesOn;
                     case inl p  => { apply Nat.le.addl Nat.zero; apply Nat.max.zeroLeft };
                     case inr np => { apply transport (_ ≤ ·); apply Nat.succPlus;
                                      apply upperEstimate (Nat.succ n) m } }
  end

  hott lemma lowerEstimate (n m : ℕ) : n ≤ BSA G n m :=
  begin
    induction m using Nat.casesOn;
    case zero   => { apply Nat.max.refl };
    case succ m => { show _ ≤ Coproduct.elim _ _ _; induction G n using Sum.casesOn;
                     case inl p  => { apply Nat.max.refl };
                     case inr np => { apply Nat.le.trans; apply Nat.le.succ;
                                      apply lowerEstimate (Nat.succ n) m } }
  end
end «3.19»

-- exercise 3.20

example {A : Type u} {B : A → Type v} (H : contr A) : (Σ x, B x) ≃ B H.1 :=
Equiv.contrFamily H

-- exercise 3.21

example (P : Type u) : prop P ≃ (P ≃ ∥P∥) :=
Equiv.propExercise P

-- exercise 3.23

namespace «3.23»
  open GroundZero.Structures
  open GroundZero.HITs

  hott def choice {A : Type u} (G : dec A) : A → Type u :=
  λ x, Coproduct.elim (x = ·) (λ φ, Empty.elim (φ x)) G

  hott def decMerely {A : Type u} (G : dec A) : Type u :=
  Σ x, choice G x

  hott def decMerely.elem {A : Type u} (G : dec A) : A → decMerely G :=
  begin
    intro x; induction G using Sum.casesOn;
    case inl y => { existsi y; apply idp };
    case inr φ => { apply Empty.elim (φ x) }
  end

  hott def decMerely.uniq {A : Type u} (G : dec A) : prop (decMerely G) :=
  begin
    induction G using Sum.casesOn;
    case inl _ => { intro w₁ w₂; fapply Sigma.prod;
                    { transitivity; apply w₁.2; symmetry; apply w₂.2 };
                    { transitivity; apply transportCompositionRev;
                      apply Equiv.rewriteComp; symmetry;
                      apply Id.cancelInvComp } };
    case inr φ => { intro w₁ w₂; apply Empty.elim (φ w₁.1) }
  end

  hott def decMerely.dec {A : Type u} (G : dec A) : dec (@decMerely A G) :=
  begin
    induction G using Sum.casesOn;
    case inl x => { left; existsi x; apply idp };
    case inr φ => { right; intro w; apply φ w.1 }
  end

  -- so for decidable type propositional truncation can be constructed explicitly (i.e. without HITs)
  hott corollary decMerelyEqvMerely {A : Type u} (G : dec A) : ∥A∥ ≃ decMerely G :=
  begin
    apply propEquivLemma; apply Merely.uniq; apply decMerely.uniq;
    apply Merely.rec; apply decMerely.uniq; apply decMerely.elem;
    { intro w; apply Merely.elem; exact w.1 }
  end

  variable {P : ℕ → Type u} (G : Π n, dec (P n))
  open «3.19»

  hott theorem elimMerelyDecFamily : ∥Σ n, P n∥ → Σ n, P n :=
  begin
    fapply Function.comp; exact (Σ n, decMerely (G n));
    intro w; existsi w.1; exact w.2.1; apply Function.comp;
    apply elimMerelyDecPropFamily;
    { intro n; apply decMerely.uniq (G n) };
    { intro n; apply decMerely.dec (G n) };
    { apply Merely.lift; intro w; existsi w.1;
      apply decMerely.elem; exact w.2 }
  end
end «3.23»
