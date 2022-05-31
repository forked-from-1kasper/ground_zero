import GroundZero.Structures
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types

/-
  Univalence axiom formulated using equivalence J-rule.

  ua, idtoeqv, compRule, propUniq
  * HoTT 2.10

  Full univalence: (α ≃ β) ≃ (α = β).

  Proof that Type is not a set.
  * HoTT 3.1, example 3.1.9
-/

namespace GroundZero

universe u v u' v'

axiom J {π : Π (α β : Type u), α ≃ β → Type v}
  (h : Π (α : Type u), π α α (ideqv α))
  {α β : Type u} (e : α ≃ β) : π α β e

attribute [eliminator] J

axiom Jβrule {π : Π (α β : Type u), α ≃ β → Type v}
  {h : Π (α : Type u), π α α (ideqv α)} {α : Type u} :
  J h (ideqv α) = h α

noncomputable hott def Jrule (π : Π (α β : Type u), α ≃ β → Type v)
  (h : Π (α : Type u), π α α (ideqv α)) {α β : Type u} (e : α ≃ β) : π α β e :=
J h e

noncomputable hott def ua {α β : Type u} : α ≃ β → α = β :=
Jrule (λ α β _, α = β) idp

namespace ua

noncomputable hott def reflOnUa (α : Type u) : ua (ideqv α) = idp α :=
by apply Jβrule

noncomputable hott def transportRule {α β : Type u} (e : α ≃ β) (x : α) :
  transportconst (ua e) x = e x :=
begin
  induction e; transitivity;
  apply Id.map (transport id · x);
  apply reflOnUa; reflexivity
end

noncomputable hott def transportInvRule {α β : Type u} (e : α ≃ β) (x : β) :
  transportconst (ua e)⁻¹ x = e.left x :=
begin
  induction e; transitivity;
  apply Id.map (transport id ·⁻¹ x);
  apply reflOnUa; reflexivity
end

noncomputable hott def compRule {α β : Type u} (e : α ≃ β) (x : α) : x =[id, ua e] e x :=
transportRule e x

hott def idtoeqvAndId {α : Type u} : idtoeqv (idp α) = ideqv α :=
by reflexivity

noncomputable hott def uaβrule {α β : Type u} (e : α ≃ β) : idtoeqv (ua e) = e :=
begin induction e; change _ = idtoeqv (idp _); apply Id.map; apply reflOnUa end

noncomputable hott def propUniq {α β : Type u} (p : α = β) : ua (idtoeqv p) = p :=
begin induction p; exact Jβrule end

noncomputable hott def univalence (α β : Type u) : (α ≃ β) ≃ (α = β) :=
⟨ua, (⟨idtoeqv, uaβrule⟩, ⟨idtoeqv, propUniq⟩)⟩

noncomputable hott def propext {α β : Type u}
  (F : prop α) (G : prop β) : (α ↔ β) → α = β :=
λ h, ua (propEquivLemma F G h.left h.right)

noncomputable hott def uaTrans {α β γ : Type u} (p : α ≃ β) (q : β ≃ γ) :
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

noncomputable hott def coproductSet {α β : Type}
  (f : hset α) (g : hset β) : hset (α + β)
| Coproduct.inl x, Coproduct.inl y =>
  transport prop (ua (@Coproduct.inl.inj' α β x y))⁻¹ (f _ _)
| Coproduct.inl x, Coproduct.inr y =>
  transport prop (ua (@Coproduct.inl.inlInr α β x y))⁻¹ emptyIsProp
| Coproduct.inr x, Coproduct.inl y =>
  transport prop (ua (@Coproduct.inr.inrInl α β x y))⁻¹ emptyIsProp
| Coproduct.inr x, Coproduct.inr y =>
  transport prop (ua (@Coproduct.inr.inj' α β x y))⁻¹ (g _ _)

-- exercise 2.17 (i) in HoTT book
noncomputable hott def productEquiv₁ {α α' β β' : Type u}
  (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') :=
begin
  have p := ua e₁; have q := ua e₂;
  induction p; induction q; apply ideqv
end

noncomputable hott def productEquiv₂ {α α' β β' : Type u}
  (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') :=
begin induction e₁; induction e₂; reflexivity end

section
  open GroundZero.Types.Product

  hott def productEquiv₃ {α : Type u} {α' : Type v} {β : Type u'} {β' : Type v'}
    (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') :=
  begin
    existsi (Product.bimap e₁.forward e₂.forward); apply Prod.mk;
    { existsi (Product.bimap e₁.left e₂.left); intro ⟨a, b⟩;
      apply prod; apply e₁.leftForward; apply e₂.leftForward };
    { existsi (Product.bimap e₁.right e₂.right); intro ⟨a, b⟩;
      apply prod; apply e₁.forwardRight; apply e₂.forwardRight }
  end
end

section
  variable {π : 𝟐 → Type u}

  hott def familyOnBool.sec (w : π false × π true) : Π b, π b
  | false => w.1
  | true  => w.2

  hott def familyOnBool.ret (φ : Π b, π b) : π false × π true :=
  (φ false, φ true)

  hott def familyOnBool : (π false × π true) ≃ Π b, π b :=
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