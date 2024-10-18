import GroundZero.Theorems.Functions
import GroundZero.Theorems.Equiv

open GroundZero.HITs.Interval (happly)
open GroundZero.Theorems.Equiv
open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto

/-
  Univalence axiom: (A ≃ B) ≃ (A = B).
  * HoTT 2.10

  Proof that Type is not a set.
  * HoTT 3.1, example 3.1.9
-/

namespace GroundZero

universe u v w u' v' w'

section
  variable {A B : Type u} (f : A → B) (g : B → A)

  hott axiom uaweak  (H : f ∘ g ~ idfun) (G : g ∘ f ~ idfun) : A = B
  hott axiom uaweakβ (H : f ∘ g ~ idfun) (G : g ∘ f ~ idfun) : transportconst (uaweak f g H G) ~ f
end

noncomputable hott definition ua {A B : Type u} (e : A ≃ B) : A = B :=
uaweak e.forward e.left e.forwardLeft e.leftForward

noncomputable hott definition uaε {A B : Type u} (e : A ≃ B) : A = B :=
ua e ⬝ (ua (ideqv B))⁻¹

noncomputable hott lemma idtoeqvua {A B : Type u} (e : A ≃ B) : idtoeqv (ua e) = e :=
begin apply equivHmtpyLem; apply uaweakβ end

noncomputable hott lemma uaidtoeqvε {A B : Type u} (p : A = B) : uaε (idtoeqv p) = p :=
begin induction p; apply Id.compInv end

noncomputable hott theorem univalence (A B : Type u) : (A = B) ≃ (A ≃ B) :=
⟨idtoeqv, (⟨uaε, uaidtoeqvε⟩, ⟨ua, idtoeqvua⟩)⟩

noncomputable hott corollary uaidtoeqv {A B : Type u} (p : A = B) : ua (idtoeqv p) = p :=
(univalence A B).rightForward p

hott example {A : Type u} : idtoeqv (idp A) = ideqv A :=
by reflexivity

noncomputable hott corollary uaidp (A : Type u) : ua (ideqv A) = idp A :=
uaidtoeqv (idp A)

noncomputable hott theorem uaβ {A B : Type u} (e : A ≃ B) (x : A) : transportconst (ua e) x = e x :=
happly (ap Equiv.forward (idtoeqvua e)) x

noncomputable hott theorem uaβrev {A B : Type u} (e : A ≃ B) (x : B) : transportconst (ua e)⁻¹ x = e.left x :=
happly (ap Equiv.left (idtoeqvua e)) x

noncomputable hott remark uaCompRule {A B : Type u} (e : A ≃ B) (x : A) : x =[id, ua e] e x :=
uaβ e x

noncomputable hott theorem propext {A B : Type u}
  (F : prop A) (G : prop B) : (A ↔ B) → A = B :=
λ h, ua (propEquivLemma F G h.left h.right)

noncomputable hott theorem uacom {A B C : Type u} (p : A ≃ B) (q : B ≃ C) : ua (p.trans q) = ua p ⬝ ua q :=
begin
  fapply (univalence A C).eqvInj; apply equivHmtpyLem;
  intro x; symmetry; transitivity; apply transportcom;
  transitivity; apply uaβ; transitivity; apply ap q;
  apply uaβ; symmetry; apply uaβ
end

noncomputable hott theorem univAlt (A : Type u) : contr (Σ B, A ≃ B) :=
begin
  existsi ⟨A, ideqv A⟩; intro w; fapply Sigma.prod; apply ua w.2;
  transitivity; apply transportMeetSigma; apply equivHmtpyLem; intro x;
  transitivity; apply happly; apply transportImpl (λ _, A) (λ B, B);
  transitivity; apply uaβ; apply ap w.2; apply transportOverConstFamily
end

noncomputable hott corollary uaSinglProp (A : Type u) : prop (Σ B, A ≃ B) :=
contrImplProp (univAlt A)

namespace Equiv
  variable {C : Π (A B : Type u), A ≃ B → Type v} (Cidp : Π (A : Type u), C A A (ideqv A))

  noncomputable hott definition J {A B : Type u} (e : A ≃ B) : C A B e :=
  transport (λ (w : Σ B, A ≃ B), C A w.1 w.2) ((univAlt A).2 ⟨B, e⟩) (Cidp A)

  attribute [induction_eliminator] J

  noncomputable hott lemma Jβrule (A : Type u) : J Cidp (ideqv A) = Cidp A :=
  begin
    dsimp [J]; transitivity; apply ap (transport _ · _);
    show _ = idp _; apply propIsSet; apply uaSinglProp; reflexivity
  end
end Equiv

hott definition isZero : ℕ → 𝟐
| Nat.zero   => true
| Nat.succ _ => false

hott example (h : 0 = 1) : 𝟎 :=
ffNeqTt (ap isZero h)⁻¹

hott lemma succNeqZero {n : ℕ} : ¬(Nat.succ n = 0) :=
λ h, ffNeqTt (ap isZero h)

hott definition negNeg : Π x, not (not x) = x
| true  => idp true
| false => idp false

hott definition negBoolEquiv : 𝟐 ≃ 𝟐 :=
⟨not, (⟨not, negNeg⟩, ⟨not, negNeg⟩)⟩

noncomputable hott theorem universeNotASet : ¬(hset Type) :=
begin
  let p : 𝟐 = 𝟐 := ua negBoolEquiv; let h := transportconst p true;
  let g : h = false := uaβ negBoolEquiv true;
  intro ε; let f : h = true := ap (transportconst · true) (ε _ _ p (idp 𝟐));
  apply ffNeqTt; exact g⁻¹ ⬝ f
end

hott theorem coproductSet {A B : Type u} (f : hset A) (g : hset B) : hset (A + B)
| Coproduct.inl x, Coproduct.inl y =>
  propRespectsEquiv (@Coproduct.inl.inj' A B x y).symm (f _ _)
| Coproduct.inl x, Coproduct.inr y =>
  propRespectsEquiv (@Coproduct.inl.inlInr A B x y).symm emptyIsProp
| Coproduct.inr x, Coproduct.inl y =>
  propRespectsEquiv (@Coproduct.inr.inrInl A B x y).symm emptyIsProp
| Coproduct.inr x, Coproduct.inr y =>
  propRespectsEquiv (@Coproduct.inr.inj' A B x y).symm (g _ _)

-- exercise 2.17 (i) in HoTT book
noncomputable hott theorem productEquiv₁ {A A' B B' : Type u}
  (e₁ : A ≃ A') (e₂ : B ≃ B') : (A × B) ≃ (A' × B') :=
begin
  have p := ua e₁; have q := ua e₂;
  induction p; induction q; apply ideqv
end

noncomputable hott theorem productEquiv₂ {A A' B B' : Type u}
  (e₁ : A ≃ A') (e₂ : B ≃ B') : (A × B) ≃ (A' × B') :=
begin induction e₁; induction e₂; reflexivity end

section
  open GroundZero.Types.Product
  variable {A : Type u} {A' : Type v} {B : Type u'} {B' : Type v'}

  hott theorem productEquiv₃ (e₁ : A ≃ A') (e₂ : B ≃ B') : (A × B) ≃ (A' × B') :=
  prodEquiv e₁ e₂
end

section
  variable {C : 𝟐 → Type u}

  hott definition familyOnBool.sec (w : C false × C true) : Π b, C b
  | false => w.1
  | true  => w.2

  hott definition familyOnBool.ret (φ : Π b, C b) : C false × C true :=
  (φ false, φ true)

  hott theorem familyOnBool : (C false × C true) ≃ Π b, C b :=
  begin
    existsi familyOnBool.sec; apply Qinv.toBiinv;
    existsi familyOnBool.ret; apply Prod.mk;
    { intro φ; apply HITs.Interval.funext; intro b;
      induction b using Bool.casesOn <;> reflexivity };
    { intro w; reflexivity }
  end
end

namespace Theorems.Equiv

noncomputable hott definition propEqProp {A B : Type u} (G : prop B) : prop (A = B) :=
begin
  apply propRespectsEquiv.{u, u + 1}; apply Equiv.symm;
  apply univalence; apply propEquivProp G
end

noncomputable hott theorem propsetIsSet : hset (Prop u) :=
begin
  intro ⟨x, H⟩ ⟨y, G⟩; apply transport (λ X, Π (p q : X), p = q);
  symmetry; apply ua; apply Sigma.sigmaPath;
  intro ⟨p, p'⟩ ⟨q, q'⟩; fapply Sigma.prod;
  { apply propEqProp; exact G };
  { apply propIsSet; apply propIsProp }
end

hott definition bool.decode : 𝟐 ≃ 𝟐 → 𝟐 :=
λ e, e false

hott definition bool.encode : 𝟐 → 𝟐 ≃ 𝟐
| false => ideqv 𝟐
| true  => negBoolEquiv

hott exercise boolEquivEqvBool : (𝟐 ≃ 𝟐) ≃ 𝟐 :=
begin
  existsi bool.decode; fapply Qinv.toBiinv; existsi bool.encode; apply Prod.mk;
  { intro x; induction x using Bool.casesOn <;> reflexivity };
  { intro ⟨φ, H⟩; apply equivHmtpyLem; intro x;
    match boolEqTotal (φ false), boolEqTotal (φ true) with
    | Sum.inl p₁, Sum.inl q₁ => { apply explode; apply ffNeqTt;
                                  apply eqvInj ⟨φ, H⟩; exact p₁ ⬝ q₁⁻¹ }
    | Sum.inr p₂, Sum.inl q₁ => { transitivity; apply ap (bool.encode · x); apply p₂;
                                  symmetry; induction x using Bool.casesOn <;> assumption }
    | Sum.inl p₁, Sum.inr q₂ => { transitivity; apply ap (bool.encode · x); apply p₁;
                                  symmetry; induction x using Bool.casesOn <;> assumption }
    | Sum.inr p₂, Sum.inr q₂ => { apply explode; apply ffNeqTt;
                                  apply eqvInj ⟨φ, H⟩; exact p₂ ⬝ q₂⁻¹ } }
end

section
  variable {A : Type u} {B : Type v}

  hott definition corrOfBiinv : A ≃ B → Corr A B :=
  λ e, @corrOfQinv A B ⟨e.1, Qinv.ofBiinv e.1 e.2⟩

  hott definition biinvOfCorr : Corr A B → A ≃ B :=
  λ c, Qinv.toEquiv (qinvOfCorr c).2

  hott lemma corrLem (R : A → B → Type w) (φ : A → B) (ρ : Π x, R x (φ x))
    (H : Π x y, R x y → φ x = y) (c : Π (x : A) (y : B) (w : R x y), ρ x =[H x y w] w)
    (x : A) (y : B) : (φ x = y) ≃ (R x y) :=
  begin
    fapply Sigma.mk; { intro p; apply transport (R x) p; apply ρ }; fapply Qinv.toBiinv;
    fapply Sigma.mk; intro r; exact (H x (φ x) (ρ x))⁻¹ ⬝ H x y r; apply Prod.mk;
    { intro r; dsimp; transitivity; apply ap; symmetry; apply c x (φ x) (ρ x);
      transitivity; apply transportcom; transitivity; apply ap (transport (R x) (H x y r));
      apply transportForwardAndBack; apply c };
    { intro p; induction p; apply Id.invComp }
  end

  noncomputable hott lemma corrBiinvIdfun : corrOfBiinv ∘ @biinvOfCorr A B ~ idfun :=
  begin
    intro w; fapply Sigma.prod;
    apply Theorems.funext; intro x; apply Theorems.funext; intro y;
    change (y = (w.2.1 x).1.1) = (w.1 x y); apply ua; apply Equiv.trans;
    apply inveqv; fapply corrLem w.1 (λ x, (w.2.1 x).1.1) (λ x, (w.2.1 x).1.2)
      (λ x y ρ, ap Sigma.fst ((w.2.1 x).2 ⟨y, ρ⟩));
    { intros x y ρ; change _ = _; transitivity; symmetry;
      apply transportComp (w.1 x) Sigma.fst ((w.2.1 x).2 ⟨y, ρ⟩);
      apply apd Sigma.snd };
    apply productProp <;> { apply piProp; intros; apply contrIsProp }
  end

  hott proposition biinvCorrIdfun : biinvOfCorr ∘ @corrOfBiinv A B ~ idfun :=
  begin intro e; fapply equivHmtpyLem; intro; reflexivity end

  noncomputable hott theorem biinvEquivCorr : Corr A B ≃ (A ≃ B) :=
  begin
    existsi biinvOfCorr; fapply Qinv.toBiinv; existsi corrOfBiinv;
    apply Prod.mk; apply biinvCorrIdfun; apply corrBiinvIdfun
  end
end

noncomputable hott theorem ntypeIsSuccNType (n : ℕ₋₂) : is-(hlevel.succ n)-type (n-Type u) :=
begin
  intro ⟨X, p⟩ ⟨Y, p'⟩; apply ntypeRespectsEquiv;
  symmetry; apply Sigma.sigmaPath; fapply ntypeRespectsSigma;
  { apply ntypeRespectsEquiv.{u, u + 1}; apply Equiv.symm;
    apply univalence X Y; induction n using hlevel.casesOn;
    { existsi contrTypeEquiv p p'; intro e; fapply Sigma.prod;
      { apply Theorems.funext; intro; apply contrImplProp; exact p' };
      { apply biinvProp } };
    { fapply Functions.ntypeOverEmbedding; exact X → Y;
      apply Functions.propSigmaEmbedding;
      { intro; apply biinvProp };
      { apply piRespectsNType (hlevel.succ _);
        intro; exact p' } } };
  { intro q; apply Structures.propIsNType; apply ntypeIsProp }
end

noncomputable hott corollary ensIsGroupoid : groupoid (0-Type) :=
begin apply oneEqvGroupoid.forward; apply ntypeIsSuccNType 0 end

noncomputable hott corollary pathNType₁ {A B : Type u} {n : ℕ₋₂} :
  is-(n + 1)-type B → is-(n + 1)-type (A = B) :=
begin
  intro H; apply ntypeRespectsEquiv.{u, u + 1};
  apply (univalence A B).symm; apply equivNType₁; exact H
end

noncomputable hott corollary pathNType₂ {A B : Type u} {n : ℕ₋₂} :
  is-(n + 1)-type A → is-(n + 1)-type (A = B) :=
begin
  intro H; apply ntypeRespectsEquiv.{u, u + 1}; apply symm;
  apply univalence; apply equivNType₂; exact H
end

end Theorems.Equiv

end GroundZero
