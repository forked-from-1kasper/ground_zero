import GroundZero.Algebra.Group.Basic
open GroundZero.Theorems.Functions GroundZero.Theorems.Equiv
open GroundZero.Types.Equiv (idtoeqv)
open GroundZero.Types.Id (dotted)
open GroundZero.ua (uaβrule)
open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.Algebra
universe u v

noncomputable hott def ntypeIsSuccNType (n : ℕ₋₂) :
  is-(hlevel.succ n)-type (nType.{u} n) :=
begin
  intro ⟨X, p⟩ ⟨Y, p'⟩; apply ntypeRespectsEquiv;
  symmetry; apply Sigma.sigmaPath; fapply ntypeRespectsSigma;
  { apply ntypeRespectsEquiv; apply ua.univalence X Y;
    induction n using hlevel.casesOn;
    { existsi contrTypeEquiv p p'; intro e; fapply Sigma.prod;
      { apply Theorems.funext; intro; apply contrImplProp; exact p' };
      { apply biinvProp } };
    { fapply ntypeOverEmbedding; exact X → Y; apply propSigmaEmbedding;
      { intro; apply biinvProp };
      { apply piRespectsNType (hlevel.succ _);
        intro; exact p' } } };
  { intro q; apply Structures.propIsNType; apply ntypeIsProp }
end

noncomputable hott def ensIsGroupoid : groupoid (0-Type) :=
begin apply oneEqvGroupoid.forward; apply ntypeIsSuccNType 0 end

private structure K1.aux :=
(val : 𝟏)

def K1 (G : Group) := K1.aux

namespace K1
  variable {G : Group}
  attribute [nothott] K1.aux.recOn K1.aux.rec aux.val

  hott def base : K1 G := ⟨★⟩

  axiom grpd     : groupoid (K1 G)
  axiom loop     : G.carrier → @Id (K1 G) base base
  axiom loop.mul : Π (x y : G.carrier), loop (G.φ x y) = loop x ⬝ loop y

  @[hottAxiom] def ind {C : K1 G → Type v}
    (baseπ : C base) (loopπ : Π (x : G.carrier), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : G.carrier),
      loopπ (G.φ x y) =[λ p, baseπ =[p] baseπ, loop.mul x y]
        loopπ x ⬝′ loopπ y)
    (groupoidπ : Π x, groupoid (C x)) : Π x, C x
  | ⟨★⟩ => baseπ

  attribute [eliminator] ind

  @[hottAxiom] def rec {C : Type v} (baseπ : C)
    (loopπ : G.carrier → baseπ = baseπ)
    (mulπ : Π x y, loopπ (G.φ x y) = loopπ x ⬝ loopπ y)
    (groupoidπ : groupoid C) : K1 G → C
  | ⟨★⟩ => baseπ

  axiom indβrule {C : K1 G → Type v}
    (baseπ : C base) (loopπ : Π (x : G.carrier), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : G.carrier),
      loopπ (G.φ x y) =[λ p, baseπ =[p] baseπ, loop.mul x y]
        loopπ x ⬝′ loopπ y)
    (groupoidπ : Π x, groupoid (C x)) :
    Π x, Equiv.apd (ind baseπ loopπ mulπ groupoidπ) (loop x) = loopπ x

  axiom recβrule {C : Type v} (baseπ : C) (loopπ : G.carrier → baseπ = baseπ)
    (mulπ : Π x y, loopπ (G.φ x y) = loopπ x ⬝ loopπ y) (groupoidπ : groupoid C) :
    Π x, Id.map (rec baseπ loopπ mulπ groupoidπ) (loop x) = loopπ x

  attribute [irreducible] K1

  instance : dotted (K1 G) := ⟨base⟩

  def KΩ.mul : Ω¹(K1 G) → Ω¹(K1 G) → Ω¹(K1 G) := λ p q, p ⬝ q
  def KΩ.one : Ω¹(K1 G)                       := idp base
  def KΩ.inv : Ω¹(K1 G) → Ω¹(K1 G)            := Id.inv

  noncomputable def KΩ (G : Group) : Group :=
  @Group.intro (Ω¹(K1 G)) (grpd _ _) KΩ.mul KΩ.inv KΩ.one
    (λ _ _ _, Id.inv (Id.assoc _ _ _))
    Id.reflLeft Id.reflRight Id.invComp

  noncomputable def homomorphism : Group.Hom G (KΩ G) :=
  Group.mkhomo loop loop.mul

  noncomputable def loop.one : @Id Ω¹(K1 G) (loop G.e) (idp base) :=
  Group.homoUnit homomorphism

  noncomputable def loop.inv : Π p, loop (G.ι p) = (loop p)⁻¹ :=
  Group.homoInv homomorphism

  noncomputable hott def family
    (baseπ : Type u)
    (loopπ : G.carrier → baseπ = baseπ)
    (mulπ  : Π x y, loopπ (G.φ x y) = loopπ x ⬝ loopπ y)
    (setπ  : hset baseπ) : K1 G → (0-Type) :=
  begin
    fapply rec;
    { existsi baseπ; apply zeroEqvSet.left; apply setπ };
    { intro x; fapply Sigma.prod; apply loopπ x; apply ntypeIsProp };
    { intros x y; symmetry;
      transitivity; symmetry; apply Sigma.prodComp;
      fapply Sigma.prodEq; { symmetry; apply mulπ };
      { apply propIsSet; apply ntypeIsProp } };
    { apply ensIsGroupoid }
  end

  noncomputable hott def code' : K1 G → (0-Type) :=
  begin
    fapply family; exact G.carrier;
    { intro x; apply ua; existsi (G.φ · x); apply Prod.mk <;>
      existsi (G.φ · (G.ι x)) <;> intro y <;> change G.φ (G.φ _ _) _ = _;
      symmetry; apply Group.cancelRight;
      symmetry; apply Group.cancelLeft };
    { intros x y; symmetry; transitivity;
      { symmetry; apply ua.uaTrans };
      apply Id.map ua; fapply Sigma.prod;
      { apply Theorems.funext; intro; apply G.mulAssoc };
      { apply biinvProp } };
    apply G.hset
  end

  hott def code (x : K1 G) := (code' x).fst

  noncomputable hott def code.hset (z : K1 G) : hset (code z) :=
  begin
    induction z; apply G.hset; apply setIsProp;
    { apply propIsSet; apply setIsProp };
    { apply oneEqvGroupoid.forward;
      apply propIsNType _ 0;
      apply setIsProp }
  end

  noncomputable hott def hsetBase : hset (@code G base) := code.hset base

  hott def encode : Π (z : K1 G), base = z → code z :=
  λ z p, Equiv.transport code p G.e

  noncomputable hott def decode (z : K1 G) : code z → base = z :=
  begin
    induction z; exact loop;
    case loopπ x =>
    { change _ = _; transitivity; apply Equiv.transportCharacterization;
      apply Theorems.funext; intro y; transitivity;
      apply Id.map (λ p, Equiv.transport (λ x, base = x) (loop x) (loop p));
      transitivity; apply Equiv.transportToTransportconst;
      transitivity; apply Id.map (Equiv.transportconst · y);
      transitivity; apply Id.mapInv; apply Id.map;
      transitivity; apply Equiv.mapOverComp;
      transitivity; apply Id.map; unfold code'; apply recβrule;
      apply Sigma.mapFstOverProd; apply ua.transportInvRule;
      transitivity; apply Equiv.transportOverInvContrMap;
      transitivity; apply Id.map; apply Equiv.idmap;
      transitivity; apply Id.map (· ⬝ loop x); apply loop.mul;
      transitivity; symmetry; apply Id.assoc;
      transitivity; apply Id.map; apply Id.map (· ⬝ loop x); apply loop.inv;
      transitivity; apply Id.map; apply Id.invComp; apply Id.reflRight };
    { apply zeroEqvSet.forward; apply piRespectsNType 0;
      intro; apply zeroEqvSet.left; apply grpd };
    { apply oneEqvGroupoid.forward;
      apply piRespectsNType 1; intro;
      apply hlevel.cumulative 0;
      apply zeroEqvSet.left; apply grpd }
  end

  noncomputable hott def encodeDecode (z : K1 G) :
    Π (p : code z), encode z (decode z p) = p :=
  begin
    induction z;
    { intro (x : G.carrier); change encode base (loop x) = _;
      transitivity; apply Equiv.transportToTransportconst;
      transitivity; apply Id.map (Equiv.transportconst · G.e);
      transitivity; apply Equiv.mapOverComp;
      transitivity; apply Id.map; unfold code'; apply recβrule;
      apply Sigma.mapFstOverProd; transitivity;
      apply ua.transportRule; apply G.oneMul };
    { apply Theorems.funext; intro; apply hsetBase };
    { apply propIsSet; apply piProp; intro; apply hsetBase };
    { apply oneEqvGroupoid.forward; apply propIsNType _ 0;
      intros p q; apply Theorems.funext; intro; apply code.hset }
  end

  noncomputable hott def decodeEncode :
    Π (z : K1 G) (p : base = z), decode z (encode z p) = p :=
  begin intros z p; induction p; apply loop.one end

  noncomputable hott def univ : G ≅ KΩ G :=
  begin
    fapply Group.mkiso; exact loop;
    { intros x y; apply loop.mul };
    apply Prod.mk <;> existsi encode base;
    apply encodeDecode; apply decodeEncode
  end
end K1

end GroundZero.Algebra