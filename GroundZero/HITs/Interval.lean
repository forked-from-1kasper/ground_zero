import GroundZero.Structures
open GroundZero.Structures GroundZero.Types
open GroundZero.Theorems (funext)
open GroundZero.Types.Equiv

namespace GroundZero
universe u v w

namespace HITs
namespace Interval
  @[hottAxiom] def segInv : i₁ = i₀ := Support.inclusion (Quot.sound (I.rel.mk true false))

  /- B i₀ and B i₁ are Prop’s, so s : b₀ = b₁ is trivial -/
  def propRec {B : I → Prop} (b₀ : B i₀) (b₁ : B i₁) : Π x, B x :=
  begin
    intro x; refine Quot.ind ?_ x; intro b;
    induction b using Bool.casesOn; exact b₀; exact b₁
  end

  def hrec (B : I → Type u) (b₀ : B 0) (b₁ : B 1) (s : HEq b₀ b₁) (x : I) : B x :=
  begin
    fapply Quot.hrecOn x;
    { intro b; induction b using Bool.casesOn; exact b₀; exact b₁ };
    { intros a b R; induction a using Bool.casesOn <;> induction b using Bool.casesOn;
      { apply HEq.refl }; { exact s }; { exact HEq.symm s }; { apply HEq.refl } }
  end

  hott def lift {B : Type u} (φ : 𝟐 → B) (H : prop B) : I → B :=
  rec (φ false) (φ true) (H _ _)

  hott def contrLeft : Π i, i₀ = i :=
  Interval.ind (idp i₀) seg (begin apply pathoverFromTrans; apply Id.reflLeft end)

  hott def contrRight : Π i, i₁ = i :=
  Interval.ind seg⁻¹ (idp i₁) (begin apply pathoverFromTrans; apply Id.invComp end)

  hott def intervalContr : contr I := ⟨i₁, contrRight⟩

  hott def intervalProp : prop I :=
  contrImplProp intervalContr

  hott def transportOverHmtpy {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g₁ g₂ : B → C) (h : A → C) (p : g₁ = g₂) (H : g₁ ∘ f ~ h) (x : A) :
       transport (λ (g : B → C), g ∘ f ~ h) p H x
    = @transport (B → C) (λ (g : B → C), g (f x) = h x) g₁ g₂ p (H x) :=
  happly (transportOverPi _ _ _) x

  hott def boolToInterval (φ : 𝟐 → 𝟐 → 𝟐) (a b : I) : I :=
  lift (λ x, lift (discrete ∘ φ x) intervalProp b) intervalProp a

  hott def neg : I → I := rec i₁ i₀ seg⁻¹
  instance : Neg I := ⟨neg⟩

  hott def min (a b : I) : I :=
  lift (λ | false => i₀ | true => a) intervalProp b

  hott def max (a b : I) : I :=
  lift (λ | false => a | true => i₁) intervalProp b

  infix:70 " ∧ " => min
  infix:70 " ∨ " => max

  hott def elim {A : Type u} {a b : A} (p : a = b) : I → A := rec a b p
  hott def lam  {A : Type u} (f : I → A) : f 0 = f 1 := Id.map f seg

  hott def connAnd {A : Type u} {a b : A}
    (p : a = b) : Π i, a = elim p i :=
  λ i, lam (λ j, elim p (i ∧ j))

  hott def cong {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : a = b) : f a = f b :=
  lam (λ i, f (elim p i))

  noncomputable hott def congRefl {A : Type u} {B : Type v}
    {a : A} (f : A → B) : cong f (idp a) = idp (f a) :=
  begin
    transitivity; apply mapOverComp;
    transitivity; apply Id.map;
    apply recβrule; reflexivity
  end

  noncomputable hott def mapEqCong {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : a = b) : Id.map f p = cong f p :=
  begin induction p; symmetry; apply congRefl end

  noncomputable hott def negNeg : Π x, neg (neg x) = x :=
  ind (idp i₀) (idp i₁) (calc
    transport (λ x, neg (neg x) = x) seg (idp i₀) =
    (@Id.map I I i₁ i₀ (neg ∘ neg) seg⁻¹) ⬝ idp i₀ ⬝ seg :
      by apply transportOverInvolution
    ... = Id.map neg (Id.map neg seg⁻¹) ⬝ idp i₀ ⬝ seg :
      begin apply Id.map (λ p, p ⬝ idp i₀ ⬝ seg);
            apply mapOverComp end
    ... = Id.map neg (Id.map neg seg)⁻¹ ⬝ idp i₀ ⬝ seg :
      begin apply Id.map (λ p, p ⬝ idp i₀ ⬝ seg);
            apply Id.map; apply Id.mapInv end
    ... = Id.map neg seg⁻¹⁻¹ ⬝ idp i₀ ⬝ seg :
      begin apply Id.map (λ p, p ⬝ idp i₀ ⬝ seg);
            apply Id.map; apply Id.map Types.Id.symm;
            apply recβrule end
    ... = Id.map neg seg ⬝ idp i₀ ⬝ seg :
      begin apply Id.map (λ (p : i₀ = i₁), Id.map neg p ⬝ idp i₀ ⬝ seg);
            apply Id.invInv end
    ... = seg⁻¹ ⬝ idp i₀ ⬝ seg :
      begin apply Id.map (· ⬝ idp i₀ ⬝ seg);
            apply recβrule end
    ... = seg⁻¹ ⬝ seg :
      begin apply Id.map (· ⬝ seg);
            apply Id.reflRight end
    ... = idp i₁ : by apply Id.invComp)

  hott def negNeg' (x : I) : neg (neg x) = x :=
  (connAnd seg⁻¹ (neg x))⁻¹ ⬝ contrRight x

  noncomputable hott def twist : I ≃ I :=
  ⟨neg, ⟨⟨neg, negNeg'⟩, ⟨neg, negNeg'⟩⟩⟩

  noncomputable hott def lineRec {A : Type u} (p : I → A) :
    rec (p 0) (p 1) (Id.map p seg) = p :=
  begin
    apply Theorems.funext; intro x; induction x;
    reflexivity; reflexivity; change _ = _;
    transitivity; apply Equiv.transportOverHmtpy;
    transitivity; apply Id.map (· ⬝ Id.map p seg);
    transitivity; apply Id.reflRight;
    transitivity; apply Id.mapInv; apply Id.map;
    apply recβrule; apply Id.invComp
  end

  noncomputable hott def transportOverSeg {A : Type u}
    (π : A → Type v) {a b : A} (p : a = b) (u : π a) :
    @transport I (λ i, π (elim p i)) 0 1 Interval.seg u = subst p u :=
  begin
    transitivity; apply transportComp;
    transitivity; apply Id.map (subst · u);
    apply recβrule; reflexivity
  end

  noncomputable hott def transportconstWithSeg {A B : Type u} (p : A = B) (x : A) :
    @transport I (elim p) 0 1 seg x = transportconst p x :=
  by apply transportOverSeg id
end Interval

end HITs
end GroundZero