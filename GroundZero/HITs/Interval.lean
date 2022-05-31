import GroundZero.Structures
open GroundZero.Structures GroundZero.Types
open GroundZero.Theorems (funext)
open GroundZero.Types.Equiv

namespace GroundZero
universe u v w

namespace HITs
namespace Interval
  @[hottAxiom] def segInv : i₁ = i₀ := Support.inclusion (Quot.sound (I.rel.mk true false))

  /- β i₀ and β i₁ are Prop’s, so s : b₀ = b₁ is trivial -/
  def propRec {β : I → Prop} (b₀ : β i₀) (b₁ : β i₁) : Π x, β x :=
  begin
    intro x; refine Quot.ind ?_ x; intro b;
    induction b using Bool.casesOn; exact b₀; exact b₁
  end

  def hrec (β : I → Type u) (b₀ : β 0) (b₁ : β 1) (s : HEq b₀ b₁) (x : I) : β x :=
  begin
    fapply Quot.hrecOn x;
    { intro b; induction b using Bool.casesOn; exact b₀; exact b₁ };
    { intros a b R; induction a using Bool.casesOn <;> induction b using Bool.casesOn;
      { apply HEq.refl }; { exact s }; { exact HEq.symm s }; { apply HEq.refl } }
  end

  hott def lift {β : Type u} (φ : 𝟐 → β) (H : prop β) : I → β :=
  rec (φ false) (φ true) (H _ _)

  hott def contrLeft : Π i, i₀ = i :=
  Interval.ind (idp i₀) seg (begin apply pathoverFromTrans; apply Id.reflLeft end)

  hott def contrRight : Π i, i₁ = i :=
  Interval.ind seg⁻¹ (idp i₁) (begin apply pathoverFromTrans; apply Id.invComp end)

  hott def intervalContr : contr I := ⟨i₁, contrRight⟩

  hott def intervalProp : prop I :=
  contrImplProp intervalContr

  hott def transportOverHmtpy {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β) (g₁ g₂ : β → γ) (h : α → γ) (p : g₁ = g₂) (H : g₁ ∘ f ~ h) (x : α) :
       transport (λ (g : β → γ), g ∘ f ~ h) p H x
    = @transport (β → γ) (λ (g : β → γ), g (f x) = h x) g₁ g₂ p (H x) :=
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

  hott def elim {α : Type u} {a b : α} (p : a = b) : I → α := rec a b p
  hott def lam  {α : Type u} (f : I → α) : f 0 = f 1 := Id.map f seg

  hott def connAnd {α : Type u} {a b : α}
    (p : a = b) : Π i, a = elim p i :=
  λ i, lam (λ j, elim p (i ∧ j))

  hott def cong {α : Type u} {β : Type v} {a b : α}
    (f : α → β) (p : a = b) : f a = f b :=
  lam (λ i, f (elim p i))

  noncomputable hott def congRefl {α : Type u} {β : Type v}
    {a : α} (f : α → β) : cong f (idp a) = idp (f a) :=
  begin
    transitivity; apply mapOverComp;
    transitivity; apply Id.map;
    apply recβrule; reflexivity
  end

  noncomputable hott def mapEqCong {α : Type u} {β : Type v} {a b : α}
    (f : α → β) (p : a = b) : Id.map f p = cong f p :=
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

  noncomputable hott def lineRec {α : Type u} (p : I → α) :
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

  noncomputable hott def transportOverSeg {α : Type u}
    (π : α → Type v) {a b : α} (p : a = b) (u : π a) :
    @transport I (λ i, π (elim p i)) 0 1 Interval.seg u = subst p u :=
  begin
    transitivity; apply transportComp;
    transitivity; apply Id.map (subst · u);
    apply recβrule; reflexivity
  end

  noncomputable hott def transportconstWithSeg {α β : Type u} (p : α = β) (x : α) :
    @transport I (elim p) 0 1 seg x = transportconst p x :=
  by apply transportOverSeg id
end Interval

end HITs
end GroundZero