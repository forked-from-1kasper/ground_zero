import GroundZero.Structures
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types

/-
  Univalence axiom formulated using equivalence J-rule.

  ua, idtoeqv, compRule, propUniq
  * HoTT 2.10

  Full univalence: (A ≃ B) ≃ (A = B).

  Proof that Type is not a set.
  * HoTT 3.1, example 3.1.9
-/

namespace GroundZero

universe u v u' v'

axiom J {C : Π (A B : Type u), A ≃ B → Type v}
  (h : Π (A : Type u), C A A (ideqv A))
  {A B : Type u} (e : A ≃ B) : C A B e

attribute [eliminator] J

axiom Jβrule {C : Π (A B : Type u), A ≃ B → Type v}
  {h : Π (A : Type u), C A A (ideqv A)} {A : Type u} :
  J h (ideqv A) = h A

noncomputable hott def Jrule (C : Π (A B : Type u), A ≃ B → Type v)
  (h : Π (A : Type u), C A A (ideqv A)) {A B : Type u} (e : A ≃ B) : C A B e :=
J h e

noncomputable hott def ua {A B : Type u} : A ≃ B → A = B :=
Jrule (λ A B _, A = B) idp

namespace ua

noncomputable hott def reflOnUa (A : Type u) : ua (ideqv A) = idp A :=
by apply Jβrule

noncomputable hott def transportRule {A B : Type u} (e : A ≃ B) (x : A) :
  transportconst (ua e) x = e x :=
begin
  induction e; transitivity;
  apply Id.map (transport id · x);
  apply reflOnUa; reflexivity
end

noncomputable hott def transportInvRule {A B : Type u} (e : A ≃ B) (x : B) :
  transportconst (ua e)⁻¹ x = e.left x :=
begin
  induction e; transitivity;
  apply Id.map (transport id ·⁻¹ x);
  apply reflOnUa; reflexivity
end

noncomputable hott def compRule {A B : Type u} (e : A ≃ B) (x : A) : x =[id, ua e] e x :=
transportRule e x

hott def idtoeqvAndId {A : Type u} : idtoeqv (idp A) = ideqv A :=
by reflexivity

noncomputable hott def uaβrule {A B : Type u} (e : A ≃ B) : idtoeqv (ua e) = e :=
begin induction e; change _ = idtoeqv (idp _); apply Id.map; apply reflOnUa end

noncomputable hott def propUniq {A B : Type u} (p : A = B) : ua (idtoeqv p) = p :=
begin induction p; exact Jβrule end

noncomputable hott def univalence (A B : Type u) : (A ≃ B) ≃ (A = B) :=
⟨ua, (⟨idtoeqv, uaβrule⟩, ⟨idtoeqv, propUniq⟩)⟩

noncomputable hott def propext {A B : Type u}
  (F : prop A) (G : prop B) : (A ↔ B) → A = B :=
λ h, ua (propEquivLemma F G h.left h.right)

noncomputable hott def uaTrans {A B γ : Type u} (p : A ≃ B) (q : B ≃ γ) :
  ua (Equiv.trans p q) = ua p ⬝ ua q :=
begin
  induction p; induction q; change ua (ideqv _) = _; symmetry;
  change _ = idp _ ⬝ _; apply Id.map (· ⬝ ua _); apply reflOnUa
end

hott def isZero : ℕ → 𝟐
| Nat.zero   => true
| Nat.succ _ => false

example (h : 0 = 1) : 𝟎 :=
ffNeqTt (Id.map isZero h)⁻¹

hott def succNeqZero {n : ℕ} : ¬(Nat.succ n = 0) :=
λ h, ffNeqTt (Id.map isZero h)

hott def negNeg : Π x, not (not x) = x
| true  => idp true
| false => idp false

hott def negBoolEquiv : 𝟐 ≃ 𝟐 :=
⟨not, (⟨not, negNeg⟩, ⟨not, negNeg⟩)⟩

noncomputable hott def universeNotASet : ¬(hset Type) :=
begin
  let p : 𝟐 = 𝟐 := ua negBoolEquiv; let h := transportconst p true;
  let g : h = false := transportRule negBoolEquiv true;
  intro ε; let f : h = true := Id.map (transportconst · true) (ε _ _ p (idp 𝟐));
  apply ffNeqTt; exact g⁻¹ ⬝ f
end

noncomputable hott def coproductSet {A B : Type}
  (f : hset A) (g : hset B) : hset (A + B)
| Coproduct.inl x, Coproduct.inl y =>
  transport prop (ua (@Coproduct.inl.inj' A B x y))⁻¹ (f _ _)
| Coproduct.inl x, Coproduct.inr y =>
  transport prop (ua (@Coproduct.inl.inlInr A B x y))⁻¹ emptyIsProp
| Coproduct.inr x, Coproduct.inl y =>
  transport prop (ua (@Coproduct.inr.inrInl A B x y))⁻¹ emptyIsProp
| Coproduct.inr x, Coproduct.inr y =>
  transport prop (ua (@Coproduct.inr.inj' A B x y))⁻¹ (g _ _)

-- exercise 2.17 (i) in HoTT book
noncomputable hott def productEquiv₁ {A A' B B' : Type u}
  (e₁ : A ≃ A') (e₂ : B ≃ B') : (A × B) ≃ (A' × B') :=
begin
  have p := ua e₁; have q := ua e₂;
  induction p; induction q; apply ideqv
end

noncomputable hott def productEquiv₂ {A A' B B' : Type u}
  (e₁ : A ≃ A') (e₂ : B ≃ B') : (A × B) ≃ (A' × B') :=
begin induction e₁; induction e₂; reflexivity end

section
  open GroundZero.Types.Product
  variable {A : Type u} {A' : Type v} {B : Type u'} {B' : Type v'}

  hott def productEquiv₃ (e₁ : A ≃ A') (e₂ : B ≃ B') : (A × B) ≃ (A' × B') :=
  prodEquiv e₁ e₂
end

section
  variable {C : 𝟐 → Type u}

  hott def familyOnBool.sec (w : C false × C true) : Π b, C b
  | false => w.1
  | true  => w.2

  hott def familyOnBool.ret (φ : Π b, C b) : C false × C true :=
  (φ false, φ true)

  hott def familyOnBool : (C false × C true) ≃ Π b, C b :=
  begin
    existsi familyOnBool.sec; apply Qinv.toBiinv;
    existsi familyOnBool.ret; apply Prod.mk;
    { intro φ; apply HITs.Interval.funext; intro b;
      induction b using Bool.casesOn <;> reflexivity };
    { intro w; reflexivity }
  end
end

end ua
end GroundZero