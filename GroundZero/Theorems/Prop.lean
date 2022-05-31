import GroundZero.HITs.Interval
import GroundZero.Theorems.UA
import GroundZero.HITs.Merely

open GroundZero.HITs.Interval
open GroundZero.Proto (idfun)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types

namespace GroundZero
namespace Theorems.Prop

universe u v w

hott def uniqDoesNotAddNewPaths {α : Type u} (a b : ∥α∥)
  (p : a = b) : HITs.Merely.uniq a b = p :=
propIsSet HITs.Merely.uniq _ _ _ _

hott def propEquiv {π : Type u} (H : prop π) : π ≃ ∥π∥ :=
propEquivLemma H HITs.Merely.uniq HITs.Merely.elem (HITs.Merely.rec H id)

hott def propFromEquiv {π : Type u} : π ≃ ∥π∥ → prop π :=
begin
  intro ⟨f, (⟨g, α⟩, _)⟩ a b; transitivity;
  exact (α a)⁻¹; symmetry; transitivity; exact (α b)⁻¹;
  apply Id.map g; exact HITs.Merely.uniq (f b) (f a)
end

hott def mapToHapply {α : Type u} {β : Type v}
  (c : α) (f g : α → β) (p : f = g) :
  Id.map (λ (f : α → β), f c) p = happly p c :=
begin induction p; reflexivity end

hott def hmtpyRewrite {α : Type u} (f : α → α) (H : f ~ id) (x : α) : H (f x) = Id.map f (H x) :=
begin have p := (Theorems.funext H)⁻¹; induction p; apply Id.symm; apply Equiv.idmap end

hott def qinvImplsIshae {α : Type u} {β : Type v} (f : α → β) : Qinv f → Ishae f :=
begin
  intro ⟨g, ⟨ε, η⟩⟩; let ε' := λ b, (ε (f (g b)))⁻¹ ⬝ (Id.map f (η (g b)) ⬝ ε b);
  existsi g; existsi η; existsi ε'; intro x; symmetry; transitivity;
  { apply Id.map (λ p, _ ⬝ (Id.map f p ⬝ _)); apply hmtpyRewrite (g ∘ f) };
  apply rewriteComp; transitivity; apply Id.map (· ⬝ _); symmetry; apply mapOverComp (g ∘ f);
  symmetry; apply @homotopySquare α β (f ∘ g ∘ f) f (λ x, ε (f x)) (g (f x)) x (η x)
end

hott def respectsEquivOverFst {α : Type u} {β : Type v}
  (φ : α ≃ β) (C : α → Type w) : (Σ x, C x) ≃ (Σ x, C (φ.left x)) :=
begin
  fapply Sigma.replaceIshae; apply qinvImplsIshae; existsi φ.1;
  apply Prod.mk; apply φ.leftForward; apply φ.forwardFeft
end

hott def fibEq {α : Type u} {β : Type v} (f : α → β) {y : β} {a b : α}
  (p : f a = y) (q : f b = y) : (Σ (γ : a = b), Id.map f γ ⬝ q = p) → @Id (fib f y) ⟨a, p⟩ ⟨b, q⟩ :=
begin
  intro ⟨γ, r⟩; fapply Sigma.prod; exact γ; transitivity; apply transportOverContrMap;
  transitivity; apply Id.map (· ⬝ p); apply Id.mapInv; apply rewriteComp; exact r⁻¹
end

hott def ishaeImplContrFib {α : Type u} {β : Type v}
  (f : α → β) : Ishae f → Π y, contr (fib f y) :=
begin
  intro ⟨g, η, ε, τ⟩ y; existsi ⟨g y, ε y⟩; intro ⟨x, p⟩; apply fibEq;
  existsi (Id.map g p)⁻¹ ⬝ η x; transitivity;
  apply Id.map (· ⬝ p); apply mapFunctoriality;
  transitivity; apply Id.map (_ ⬝ · ⬝ p); apply τ;
  transitivity; symmetry; apply Id.assoc; transitivity;
  { apply Id.map (· ⬝ _); transitivity; apply Id.mapInv;
    apply Id.map; symmetry; apply mapOverComp };
  apply rewriteComp; transitivity; apply Id.map (_ ⬝ ·);
  symmetry; apply idmap; apply homotopySquare
end


hott def compQinv₁ {α : Type u} {β : Type v} {γ : Type w}
  (f : α → β) (g : β → α) (H : isQinv f g) :
  @Qinv (γ → α) (γ → β) (f ∘ ·) :=
begin
  existsi (g ∘ ·); apply Prod.mk <;> intro <;>
  apply Theorems.funext <;> intro; apply H.1; apply H.2
end

hott def compQinv₂ {α : Type u} {β : Type v} {γ : Type w}
  (f : α → β) (g : β → α) (H : isQinv f g) :
  @Qinv (β → γ) (α → γ) (· ∘ f) :=
begin
  existsi (· ∘ g) <;> apply Prod.mk <;> intro G <;>
  apply Theorems.funext <;> intro <;>
  apply Id.map G; apply H.2; apply H.1
end

hott def linvContr {α : Type u} {β : Type v}
  (f : α → β) (H : Qinv f) : contr (linv f) :=
begin
  apply contrRespectsEquiv;
  { apply Equiv.symm; apply Sigma.respectsEquiv;
    intro g; symmetry; apply @Theorems.full α (λ _, α) (g ∘ f) };
  apply ishaeImplContrFib; apply qinvImplsIshae;
  fapply compQinv₂; exact H.1; exact H.2
end

hott def rinvContr {α : Type u} {β : Type v}
  (f : α → β) (H : Qinv f) : contr (rinv f) :=
begin
  apply contrRespectsEquiv;
  { apply Equiv.symm; apply Sigma.respectsEquiv;
    intro g; symmetry; apply @Theorems.full β (λ _, β) (f ∘ g) };
  apply ishaeImplContrFib; apply qinvImplsIshae;
  fapply compQinv₁; exact H.1; exact H.2
end

hott def productContr {α : Type u} {β : Type v} (h : contr α) (g : contr β) : contr (α × β) :=
begin existsi (h.1, g.1); intro p; fapply Product.prod; apply h.2; apply g.2 end

hott def biinvProp {α : Type u} {β : Type v} (f : α → β) : prop (biinv f) :=
begin
  apply lemContr; intro g; apply productContr;
  { apply linvContr; apply Qinv.ofBiinv; assumption };
  { apply rinvContr; apply Qinv.ofBiinv; assumption }
end

hott def equivHmtpyLem {α : Type u} {β : Type v}
  (f g : α ≃ β) (H : f.forward ~ g.forward) : f = g :=
begin fapply Sigma.prod; apply Theorems.funext; exact H; apply biinvProp end

hott def propEquivProp {α β : Type u} (G : prop β) : prop (α ≃ β) :=
begin intros f g; apply equivHmtpyLem; intro x; apply G end

hott def propExercise (π : Type u) : prop π ≃ (π ≃ ∥π∥) :=
begin
  existsi @propEquiv π; apply Prod.mk <;> existsi propFromEquiv;
  { intro x; apply propIsProp };
  { intro f; apply equivHmtpyLem;
    intro x; apply HITs.Merely.uniq }
end

hott def lemContrInv {α : Type u} (h : prop α) (x : α) : contr α := ⟨x, h x⟩

hott def lemContrEquiv {α : Type u} : (prop α) ≃ (α → contr α) :=
begin
  apply propEquivLemma; apply propIsProp; apply functionToContr;
  apply lemContrInv; apply lemContr
end

hott def contrToType {α : Type u} {β : α → Type v}
  (H : contr α) : (Σ x, β x) → β H.1 :=
λ w, subst (H.2 w.1)⁻¹ w.2

hott def typeToContr {α : Type u} {β : α → Type v}
  (H : contr α) : β H.1 → (Σ x, β x) :=
λ u, ⟨H.1, u⟩

-- HoTT 3.20
hott def contrFamily {α : Type u} {β : α → Type v} (H : contr α) : (Σ x, β x) ≃ β H.1 :=
begin
  existsi contrToType H; apply Prod.mk <;>
  existsi @typeToContr α β H <;> intro x;
  { fapply Sigma.prod; apply H.2; apply transportBackAndForward };
  { transitivity; apply Id.map (subst · x);
    apply propIsSet (contrImplProp H) _ _ _ (idp _);
    reflexivity }
end

hott def propset.Id (α β : Ω) (H : α.1 = β.1) : α = β :=
Sigma.prod H (propIsProp _ _)

noncomputable hott def propEqProp {α β : Type u} (G : prop β) : prop (α = β) :=
begin apply propRespectsEquiv; apply GroundZero.ua.univalence α β; apply propEquivProp G end

noncomputable hott def propsetIsSet : hset propset :=
begin
  intro ⟨x, H⟩ ⟨y, G⟩; apply transport (λ π, Π (p q : π), p = q);
  symmetry; apply GroundZero.ua; apply Sigma.sigmaPath;
  intro ⟨p, p'⟩ ⟨q, q'⟩; fapply Sigma.prod;
  { apply propEqProp; exact G };
  { apply propIsSet; apply propIsProp }
end

hott def hsetEquiv {α : Type u} {β : Type v} (g : hset β) : hset (α ≃ β) :=
begin
  fapply hsetRespectsSigma;
  { apply piHset; intro x; assumption };
  { intro x; apply propIsSet; apply biinvProp }
end

hott def bool.decode : 𝟐 ≃ 𝟐 → 𝟐 :=
λ e, e false

hott def bool.encode : 𝟐 → 𝟐 ≃ 𝟐
| false => ideqv 𝟐
| true  => ua.negBoolEquiv

hott def eqvInj {α : Type u} {β : Type v} (e : α ≃ β) (x y : α)
  (p : e.forward x = e.forward y) : x = y :=
begin
  transitivity; symmetry; apply e.leftForward;
  transitivity; apply Id.map e.left; exact p;
  apply e.leftForward
end

hott def zeroEquiv.hset (α β : 0-Type) : hset (α ≃₀ β) :=
begin apply hsetEquiv; apply zeroEqvSet.forward; exact β.2 end

hott def boolEquivEqvBool : (𝟐 ≃ 𝟐) ≃ 𝟐 :=
begin
  existsi bool.decode; fapply Qinv.toBiinv; existsi bool.encode; apply Prod.mk;
  { intro x; induction x using Bool.casesOn <;> reflexivity };
  { intro ⟨φ, H⟩; apply equivHmtpyLem; intro x;
    match boolEqTotal (φ false), boolEqTotal (φ true) with
    | Sum.inl p₁, Sum.inl q₁ => _
    | Sum.inr p₂, Sum.inl q₁ => _
    | Sum.inl p₁, Sum.inr q₂ => _
    | Sum.inr p₂, Sum.inr q₂ => _;
    -- TODO: apply “or” here somehow
    { apply Proto.Empty.elim; apply ffNeqTt;
      apply eqvInj ⟨φ, H⟩; exact p₁ ⬝ q₁⁻¹ };
    { apply Id.trans; apply Id.map (bool.encode · x); apply p₂;
      symmetry; induction x using Bool.casesOn <;> assumption };
    { apply Id.trans; apply Id.map (bool.encode · x); apply p₁;
      symmetry; induction x using Bool.casesOn <;> assumption };
    { apply Proto.Empty.elim; apply ffNeqTt;
      apply eqvInj ⟨φ, H⟩; exact p₂ ⬝ q₂⁻¹ } }
end

hott def contrQinvFib {α : Type u} {β : Type v} (w : Qinv.eqv α β) (b : β) : contr (Σ a, b = w.1 a) :=
begin apply contrRespectsEquiv; apply respectsEquivOverFst (Qinv.toEquiv (Qinv.inv w)) (Id b); apply singl.contr end

hott def propQinvFib {α : Type u} {β : Type v} (w : Qinv.eqv α β) (b : β) : prop (Σ a, b = w.1 a) :=
contrImplProp (contrQinvFib w b)

hott def corrRev {α : Type u} {β : Type v} : Corr α β → Corr β α :=
λ w, ⟨λ a b, w.1 b a, (w.2.2, w.2.1)⟩

hott def corrOfQinv {α : Type u} {β : Type v} : Qinv.eqv α β → Corr α β :=
begin
  intro w; existsi (λ a b, b = w.1 a); apply Prod.mk <;> intros;
  apply contrRespectsEquiv; apply Sigma.hmtpyInvEqv; apply singl.contr;
  apply contrQinvFib
end

hott def qinvOfCorr {α : Type u} {β : Type v} : Corr α β → Qinv.eqv α β :=
begin
  intro w; fapply Sigma.mk; intro a; apply (w.2.1 a).1.1;
  fapply Sigma.mk; intro b; apply (w.2.2 b).1.1; apply Prod.mk;
  { intro b; apply Id.map Sigma.fst ((w.2.1 (w.2.2 b).1.1).2 ⟨b, (w.2.2 b).1.2⟩) };
  { intro a; apply Id.map Sigma.fst ((w.2.2 (w.2.1 a).1.1).2 ⟨a, (w.2.1 a).1.2⟩) }
end

section
  variable {α : Type u} {β : Type v} (e : Qinv.eqv α β)

  example : (qinvOfCorr (corrOfQinv e)).1 = e.1     := by reflexivity
  example : (qinvOfCorr (corrOfQinv e)).2.1 = e.2.1 := by reflexivity
end

section
  variable {α : Type u} {β : Type v}

  hott def corrOfBiinv : α ≃ β → Corr α β :=
  λ e, @corrOfQinv α β ⟨e.1, Qinv.ofBiinv e.1 e.2⟩

  hott def biinvOfCorr : Corr α β → α ≃ β :=
  Qinv.toEquiv ∘ qinvOfCorr

  hott def corrLem (R : α → β → Type w) (φ : α → β) (ρ : Π x, R x (φ x))
    (H : Π x y, R x y → φ x = y) (c : Π (x : α) (y : β) (w : R x y), ρ x =[H x y w] w)
    (x : α) (y : β) : (φ x = y) ≃ (R x y) :=
  begin
    fapply Sigma.mk; { intro p; apply transport (R x) p; apply ρ }; fapply Qinv.toBiinv;
    fapply Sigma.mk; intro r; exact (H x (φ x) (ρ x))⁻¹ ⬝ H x y r; apply Prod.mk;
    { intro r; dsimp; transitivity; apply Id.map; symmetry; apply c x (φ x) (ρ x);
      transitivity; apply substComp; transitivity; apply Id.map (subst (H x y r));
      apply transportForwardAndBack; apply c };
    { intro p; induction p; apply Id.invComp }
  end

  noncomputable hott def corrBiinvIdfun : corrOfBiinv ∘ @biinvOfCorr α β ~ idfun :=
  begin
    intro w; fapply Sigma.prod;
    apply Theorems.funext; intro x; apply Theorems.funext; intro y;
    change (y = (w.2.1 x).1.1) = (w.1 x y); apply ua; apply Equiv.trans;
    apply inveqv; fapply corrLem w.1 (λ x, (w.2.1 x).1.1) (λ x, (w.2.1 x).1.2)
      (λ x y ρ, Id.map Sigma.fst ((w.2.1 x).2 ⟨y, ρ⟩));
    { intros x y ρ; change _ = _; transitivity; symmetry;
      apply transportComp (w.1 x) Sigma.fst ((w.2.1 x).2 ⟨y, ρ⟩);
      apply apd Sigma.snd };
    apply productProp <;> { apply piProp; intros; apply contrIsProp }
  end

  hott def biinvCorrIdfun : biinvOfCorr ∘ @corrOfBiinv α β ~ idfun :=
  begin intro e; fapply equivHmtpyLem; intro; reflexivity end

  noncomputable hott def biinvEquivCorr : Corr α β ≃ (α ≃ β) :=
  begin
    existsi biinvOfCorr; fapply Qinv.toBiinv; existsi corrOfBiinv;
    apply Prod.mk; apply biinvCorrIdfun; apply corrBiinvIdfun
  end
end

end Theorems.Prop
end GroundZero