import GroundZero.HITs.Interval
import GroundZero.Theorems.UA
import GroundZero.HITs.Merely

open GroundZero.HITs.Interval
open GroundZero.Proto (idfun)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types

namespace GroundZero
namespace Theorems.Equiv

universe u v w w' w''

hott def uniqDoesNotAddNewPaths {A : Type u} (a b : ∥A∥)
  (p : a = b) : HITs.Merely.uniq a b = p :=
propIsSet HITs.Merely.uniq _ _ _ _

hott def propEquiv {A : Type u} (H : prop A) : A ≃ ∥A∥ :=
propEquivLemma H HITs.Merely.uniq HITs.Merely.elem (HITs.Merely.rec H id)

hott def propFromEquiv {A : Type u} : A ≃ ∥A∥ → prop A :=
begin
  intro ⟨f, (⟨g, A⟩, _)⟩ a b; transitivity;
  exact (A a)⁻¹; symmetry; transitivity; exact (A b)⁻¹;
  apply Id.map g; exact HITs.Merely.uniq (f b) (f a)
end

hott def mapToHapply {A : Type u} {B : A → Type v}
  (c : A) (f g : Π x, B x) (p : f = g) :
  Id.map (λ (f : Π x, B x), f c) p = happly p c :=
begin induction p; reflexivity end

hott def mapToHapply₂ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
  (c₁ : A) (c₂ : B c₁) (f g : Π (x : A) (y : B x), C x y) (p : f = g) :
  Id.map (λ f, f c₁ c₂) p = happly (happly p c₁) c₂ :=
begin induction p; reflexivity end

hott def mapToHapply₃ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
  {D : Π x y, C x y → Type w'} (c₁ : A) (c₂ : B c₁) (c₃ : C c₁ c₂) (f g : Π x y z, D x y z) (p : f = g) :
  Id.map (λ f, f c₁ c₂ c₃) p = happly (happly (happly p c₁) c₂) c₃ :=
begin induction p; reflexivity end

hott def mapToHapply₄ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
  {D : Π (x : A) (y : B x), C x y → Type w'} {E : Π (x : A) (y : B x) (z : C x y), D x y z → Type w''}
  (c₁ : A) (c₂ : B c₁) (c₃ : C c₁ c₂) (c₄ : D c₁ c₂ c₃) (f g : Π x y z w, E x y z w) (p : f = g) :
  Id.map (λ f, f c₁ c₂ c₃ c₄) p = happly (happly (happly (happly p c₁) c₂) c₃) c₄ :=
begin induction p; reflexivity end

hott def happlyFunextPt {A : Type u} {B : A → Type v} {f g : Π x, B x} (H : f ~ g) (x : A) : happly (funext H) x = H x :=
begin apply happly; apply happlyFunext end

hott def happlyFunextPt₂ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
  {f g : Π x y, C x y} (H : Π x y, f x y = g x y) (c₁ : A) (c₂ : B c₁) :
  happly (happly (funext (λ x, funext (H x))) c₁) c₂ = H c₁ c₂ :=
begin transitivity; apply Id.map (happly · c₂); apply happlyFunextPt; apply happlyFunextPt end

hott def happlyFunextPt₃ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
  {D : Π x y, C x y → Type w'} {f g : Π x y z, D x y z}
  (H : Π x y z, f x y z = g x y z) (c₁ : A) (c₂ : B c₁) (c₃ : C c₁ c₂) :
  happly (happly (happly (funext (λ x, funext (λ y, funext (H x y)))) c₁) c₂) c₃ = H c₁ c₂ c₃ :=
begin transitivity; apply Id.map (happly · c₃); apply happlyFunextPt₂; apply happlyFunextPt end

hott def happlyFunextPt₄ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
  {D : Π x y, C x y → Type w'} {E : Π x y z, D x y z → Type w''} {f g : Π x y z w, E x y z w}
  (H : Π x y z w, f x y z w = g x y z w) (c₁ : A) (c₂ : B c₁) (c₃ : C c₁ c₂) (c₄ : D c₁ c₂ c₃) :
  happly (happly (happly (happly (funext (λ x, funext (λ y, funext (λ z, funext (H x y z))))) c₁) c₂) c₃) c₄ = H c₁ c₂ c₃ c₄ :=
begin transitivity; apply Id.map (happly · c₄); apply happlyFunextPt₃; apply happlyFunextPt end

hott def happlyRevPt {A : Type u} {B : A → Type v} {f g : Π x, B x} (p : f = g) (x : A) :
  happly p⁻¹ x = Homotopy.symm f g (happly p) x :=
begin apply happly; apply HITs.Interval.happlyRev end

hott def hmtpyRewrite {A : Type u} (f : A → A) (H : f ~ id) (x : A) : H (f x) = Id.map f (H x) :=
begin have p := (Theorems.funext H)⁻¹; induction p; symmetry; apply Equiv.idmap end

hott def qinvImplsIshae {A : Type u} {B : Type v} (f : A → B) : qinv f → ishae f :=
begin
  intro ⟨g, ⟨ε, η⟩⟩; let ε' := λ b, (ε (f (g b)))⁻¹ ⬝ (Id.map f (η (g b)) ⬝ ε b);
  existsi g; existsi η; existsi ε'; intro x; symmetry; transitivity;
  { apply Id.map (λ p, _ ⬝ (Id.map f p ⬝ _)); apply hmtpyRewrite (g ∘ f) };
  apply rewriteComp; transitivity; apply Id.map (· ⬝ _); symmetry; apply mapOverComp (g ∘ f);
  symmetry; apply @homotopySquare A B (f ∘ g ∘ f) f (λ x, ε (f x)) (g (f x)) x (η x)
end

hott def respectsEquivOverFst {A : Type u} {B : Type v}
  (φ : A ≃ B) (C : A → Type w) : (Σ x, C x) ≃ (Σ x, C (φ.left x)) :=
begin
  fapply Sigma.replaceIshae; apply qinvImplsIshae; existsi φ.1;
  apply Prod.mk; apply φ.leftForward; apply φ.forwardLeft
end

hott def fibEq {A : Type u} {B : Type v} (f : A → B) {y : B} {a b : A}
  (p : f a = y) (q : f b = y) : (Σ (γ : a = b), Id.map f γ ⬝ q = p) → @Id (fib f y) ⟨a, p⟩ ⟨b, q⟩ :=
begin
  intro ⟨γ, r⟩; fapply Sigma.prod; exact γ; transitivity; apply transportOverContrMap;
  transitivity; apply Id.map (· ⬝ p); apply Id.mapInv; apply rewriteComp; exact r⁻¹
end

hott def ishaeImplContrFib {A : Type u} {B : Type v}
  (f : A → B) : ishae f → Π y, contr (fib f y) :=
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

hott def compQinv₁ {A : Type u} {B : Type v} {C : Type w}
  (f : A → B) (g : B → A) (H : isQinv f g) :
  @qinv (C → A) (C → B) (f ∘ ·) :=
begin
  existsi (g ∘ ·); apply Prod.mk <;> intro <;>
  apply Theorems.funext <;> intro; apply H.1; apply H.2
end

hott def compQinv₂ {A : Type u} {B : Type v} {C : Type w}
  (f : A → B) (g : B → A) (H : isQinv f g) :
  @qinv (B → C) (A → C) (· ∘ f) :=
begin
  existsi (· ∘ g) <;> apply Prod.mk <;> intro G <;>
  apply Theorems.funext <;> intro <;>
  apply Id.map G; apply H.2; apply H.1
end

hott def linvContr {A : Type u} {B : Type v}
  (f : A → B) (H : qinv f) : contr (linv f) :=
begin
  apply contrRespectsEquiv;
  { apply Equiv.symm; apply Sigma.respectsEquiv;
    intro g; symmetry; apply @Theorems.full A (λ _, A) (g ∘ f) };
  apply ishaeImplContrFib; apply qinvImplsIshae;
  fapply compQinv₂; exact H.1; exact H.2
end

hott def rinvContr {A : Type u} {B : Type v}
  (f : A → B) (H : qinv f) : contr (rinv f) :=
begin
  apply contrRespectsEquiv;
  { apply Equiv.symm; apply Sigma.respectsEquiv;
    intro g; symmetry; apply @Theorems.full B (λ _, B) (f ∘ g) };
  apply ishaeImplContrFib; apply qinvImplsIshae;
  fapply compQinv₁; exact H.1; exact H.2
end

hott def productContr {A : Type u} {B : Type v} (h : contr A) (g : contr B) : contr (A × B) :=
begin existsi (h.1, g.1); intro p; fapply Product.prod; apply h.2; apply g.2 end

hott def biinvProp {A : Type u} {B : Type v} (f : A → B) : prop (biinv f) :=
begin
  apply lemContr; intro g; apply productContr;
  { apply linvContr; apply Qinv.ofBiinv; assumption };
  { apply rinvContr; apply Qinv.ofBiinv; assumption }
end

hott def equivHmtpyLem {A : Type u} {B : Type v}
  (f g : A ≃ B) (H : f.forward ~ g.forward) : f = g :=
begin fapply Sigma.prod; apply Theorems.funext; exact H; apply biinvProp end

hott def propEquivProp {A B : Type u} (G : prop B) : prop (A ≃ B) :=
begin intros f g; apply equivHmtpyLem; intro x; apply G end

hott def propExercise (π : Type u) : prop π ≃ (π ≃ ∥π∥) :=
begin
  existsi @propEquiv π; apply Prod.mk <;> existsi propFromEquiv;
  { intro x; apply propIsProp };
  { intro f; apply equivHmtpyLem;
    intro x; apply HITs.Merely.uniq }
end

hott def lemContrInv {A : Type u} (h : prop A) (x : A) : contr A := ⟨x, h x⟩

hott def lemContrEquiv {A : Type u} : (prop A) ≃ (A → contr A) :=
begin
  apply propEquivLemma; apply propIsProp; apply functionToContr;
  apply lemContrInv; apply lemContr
end

hott def contrToType {A : Type u} {B : A → Type v}
  (H : contr A) : (Σ x, B x) → B H.1 :=
λ w, subst (H.2 w.1)⁻¹ w.2

hott def typeToContr {A : Type u} {B : A → Type v}
  (H : contr A) : B H.1 → (Σ x, B x) :=
λ u, ⟨H.1, u⟩

-- HoTT 3.20
hott def contrFamily {A : Type u} {B : A → Type v} (H : contr A) : (Σ x, B x) ≃ B H.1 :=
begin
  existsi contrToType H; apply Prod.mk <;>
  existsi @typeToContr A B H <;> intro x;
  { fapply Sigma.prod; apply H.2; apply transportBackAndForward };
  { transitivity; apply Id.map (subst · x);
    apply propIsSet (contrImplProp H) _ _ _ (idp _);
    reflexivity }
end

hott def propset.Id (A B : Prop) (H : A.1 = B.1) : A = B :=
Sigma.prod H (propIsProp _ _)

noncomputable hott def propEqProp {A B : Type u} (G : prop B) : prop (A = B) :=
begin apply propRespectsEquiv; apply GroundZero.ua.univalence A B; apply propEquivProp G end

noncomputable hott def propsetIsSet : hset propset :=
begin
  intro ⟨x, H⟩ ⟨y, G⟩; apply transport (λ π, Π (p q : π), p = q);
  symmetry; apply GroundZero.ua; apply Sigma.sigmaPath;
  intro ⟨p, p'⟩ ⟨q, q'⟩; fapply Sigma.prod;
  { apply propEqProp; exact G };
  { apply propIsSet; apply propIsProp }
end

hott def hsetEquiv {A : Type u} {B : Type v} (g : hset B) : hset (A ≃ B) :=
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

hott def zeroEquiv.hset (A B : 0-Type) : hset (A ≃₀ B) :=
begin apply hsetEquiv; apply zeroEqvSet.forward; exact B.2 end

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
    { transitivity; apply Id.map (bool.encode · x); apply p₂;
      symmetry; induction x using Bool.casesOn <;> assumption };
    { transitivity; apply Id.map (bool.encode · x); apply p₁;
      symmetry; induction x using Bool.casesOn <;> assumption };
    { apply Proto.Empty.elim; apply ffNeqTt;
      apply eqvInj ⟨φ, H⟩; exact p₂ ⬝ q₂⁻¹ } }
end

hott def contrQinvFib {A : Type u} {B : Type v} {f : A → B} (e : qinv f) (b : B) : contr (Σ a, b = f a) :=
begin apply contrRespectsEquiv; apply respectsEquivOverFst (Qinv.toEquiv (Qinv.sym e)) (Id b); apply singl.contr end

hott def propQinvFib {A : Type u} {B : Type v} {f : A → B} (e : qinv f) (b : B) : prop (Σ a, b = f a) :=
contrImplProp (contrQinvFib e b)

hott def corrRev {A : Type u} {B : Type v} : Corr A B → Corr B A :=
λ w, ⟨λ a b, w.1 b a, (w.2.2, w.2.1)⟩

hott def corrOfQinv {A : Type u} {B : Type v} : (Σ f, @qinv A B f) → Corr A B :=
begin
  intro w; existsi (λ a b, b = w.1 a); apply Prod.mk <;> intros;
  apply contrRespectsEquiv; apply Sigma.hmtpyInvEqv; apply singl.contr;
  apply contrQinvFib; exact w.2
end

hott def qinvOfCorr {A : Type u} {B : Type v} : Corr A B → (Σ f, @qinv A B f) :=
begin
  intro w; fapply Sigma.mk; intro a; apply (w.2.1 a).1.1;
  fapply Sigma.mk; intro b; apply (w.2.2 b).1.1; apply Prod.mk;
  { intro b; apply Id.map Sigma.fst ((w.2.1 (w.2.2 b).1.1).2 ⟨b, (w.2.2 b).1.2⟩) };
  { intro a; apply Id.map Sigma.fst ((w.2.2 (w.2.1 a).1.1).2 ⟨a, (w.2.1 a).1.2⟩) }
end

section
  variable {A : Type u} {B : Type v} (e : Σ f, @qinv A B f)

  example : (qinvOfCorr (corrOfQinv e)).1 = e.1     := by reflexivity
  example : (qinvOfCorr (corrOfQinv e)).2.1 = e.2.1 := by reflexivity
end

section
  variable {A : Type u} {B : Type v}

  hott def corrOfBiinv : A ≃ B → Corr A B :=
  λ e, @corrOfQinv A B ⟨e.1, Qinv.ofBiinv e.1 e.2⟩

  hott def biinvOfCorr : Corr A B → A ≃ B :=
  λ c, Qinv.toEquiv (qinvOfCorr c).2

  hott def corrLem (R : A → B → Type w) (φ : A → B) (ρ : Π x, R x (φ x))
    (H : Π x y, R x y → φ x = y) (c : Π (x : A) (y : B) (w : R x y), ρ x =[H x y w] w)
    (x : A) (y : B) : (φ x = y) ≃ (R x y) :=
  begin
    fapply Sigma.mk; { intro p; apply transport (R x) p; apply ρ }; fapply Qinv.toBiinv;
    fapply Sigma.mk; intro r; exact (H x (φ x) (ρ x))⁻¹ ⬝ H x y r; apply Prod.mk;
    { intro r; dsimp; transitivity; apply Id.map; symmetry; apply c x (φ x) (ρ x);
      transitivity; apply substComp; transitivity; apply Id.map (subst (H x y r));
      apply transportForwardAndBack; apply c };
    { intro p; induction p; apply Id.invComp }
  end

  noncomputable hott def corrBiinvIdfun : corrOfBiinv ∘ @biinvOfCorr A B ~ idfun :=
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

  hott def biinvCorrIdfun : biinvOfCorr ∘ @corrOfBiinv A B ~ idfun :=
  begin intro e; fapply equivHmtpyLem; intro; reflexivity end

  noncomputable hott def biinvEquivCorr : Corr A B ≃ (A ≃ B) :=
  begin
    existsi biinvOfCorr; fapply Qinv.toBiinv; existsi corrOfBiinv;
    apply Prod.mk; apply biinvCorrIdfun; apply corrBiinvIdfun
  end
end

hott def pathOver {A : Type u} (B : A → Type v) {a b : A} (p : a = b) (u : B a) (v : B b) :=
Σ (φ : Π x y, x = y → B x → B y), φ a b p u = v × Π x, φ x x (idp x) ~ idfun

hott def pathOverCharacterization {A : Type u} {B : A → Type v} {a b : A}
  (p : a = b) (u : B a) (v : B b) : (u =[p] v) ≃ pathOver B p u v :=
begin
  fapply Sigma.mk; { intro q; existsi @transport A B; apply Prod.mk; exact q; intro; apply idp };
  apply Qinv.toBiinv; fapply Sigma.mk; { intro ω; induction p; apply (ω.2.2 a u)⁻¹ ⬝ ω.2.1 };
  apply Prod.mk;
  { induction p; intro ω; fapply Sigma.prod;
    { apply Theorems.funext; intro x;
      apply Theorems.funext; intro y;
      apply Theorems.funext; intro η;
      induction η; apply Theorems.funext (λ w, (ω.2.2 x w)⁻¹) };
    transitivity; apply transportOverProduct; apply Product.prod;
    transitivity; apply transportOverContrMap;
    { transitivity; apply Id.map (· ⬝ _);
      transitivity; apply Id.mapInv; apply Id.map Id.inv;
      transitivity; apply mapToHapply₄;
      transitivity; apply Id.map (happly · _);
      apply happlyFunextPt₃; apply happlyFunextPt; apply Id.invCompCancel };
    { transitivity; apply transportOverPi; apply Theorems.funext; intro;
      transitivity; apply transportOverPi; apply Theorems.funext; intro;
      transitivity; apply transportOverContrMap;
      transitivity; apply Id.reflRight;
      transitivity; apply Id.mapInv;
      transitivity; apply Id.map Id.inv;
      transitivity; apply mapToHapply₄;
      transitivity; apply Id.map (happly · _);
      apply happlyFunextPt₃; apply happlyFunextPt; apply Id.invInv } };
  { induction p; reflexivity }
end

hott def replaceIshaeUnderPi {A : Type u} {B : Type v} {C : A → Type w}
  (g : B → A) (e : ishae g) : (Π x, C x) ≃ (Π x, C (g x)) :=
begin
  fapply Sigma.mk; intro φ x; exact φ (g x); fapply Qinv.toBiinv;
  fapply Sigma.mk; intro ψ y; exact transport C (e.2.2.1 y) (ψ (e.1 y)); apply Prod.mk;
  { intro ψ; apply Theorems.funext; intro;
    transitivity; apply Equiv.transportSquare; symmetry; apply e.2.2.2;
    transitivity; symmetry; apply Equiv.transportComp; apply apd };
  { intro φ; apply Theorems.funext; intro; apply apd }
end

hott def replaceQinvUnderPi {A : Type u} {B : Type v} {C : A → Type w}
  (g : B → A) : qinv g → (Π x, C x) ≃ (Π x, C (g x)) :=
replaceIshaeUnderPi g ∘ qinvImplsIshae g

end Theorems.Equiv
end GroundZero