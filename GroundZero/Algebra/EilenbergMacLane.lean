import GroundZero.Algebra.Group.Basic
import GroundZero.Theorems.Prop

open GroundZero.Theorems.Functions GroundZero.Theorems.Prop
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

def K1 (G : Pregroup) := K1.aux

namespace K1
  variable {G : Pregroup}
  local infixl:70 " * " => G.φ

  attribute [nothott] K1.aux.recOn K1.aux.rec aux.val

  hott def base : K1 G := ⟨★⟩

  axiom grpd     : groupoid (K1 G)
  axiom loop     : G.carrier → @Id (K1 G) base base
  axiom loop.mul : Π (x y : G.carrier), loop (x * y) = loop x ⬝ loop y

  @[hottAxiom] def ind {π : K1 G → Type v}
    (baseπ : π base) (loopπ : Π (x : G.carrier), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : G.carrier),
      loopπ (x * y) =[λ p, baseπ =[p] baseπ, loop.mul x y]
        loopπ x ⬝′ loopπ y)
    (groupoidπ : Π x, groupoid (π x)) : Π x, π x
  | ⟨★⟩ => baseπ

  attribute [eliminator] ind

  @[hottAxiom] def rec {π : Type v} (baseπ : π)
    (loopπ : G.carrier → baseπ = baseπ)
    (mulπ : Π x y, loopπ (x * y) = loopπ x ⬝ loopπ y)
    (groupoidπ : groupoid π) : K1 G → π
  | ⟨★⟩ => baseπ

  axiom indβrule {π : K1 G → Type v}
    (baseπ : π base) (loopπ : Π (x : G.carrier), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : G.carrier),
      loopπ (x * y) =[λ p, baseπ =[p] baseπ, loop.mul x y]
        loopπ x ⬝′ loopπ y)
    (groupoidπ : Π x, groupoid (π x)) :
    Π x, Equiv.apd (ind baseπ loopπ mulπ groupoidπ) (loop x) = loopπ x

  axiom recβrule {π : Type v} (baseπ : π) (loopπ : G.carrier → baseπ = baseπ)
    (mulπ : Π x y, loopπ (x * y) = loopπ x ⬝ loopπ y) (groupoidπ : groupoid π) :
    Π x, Id.map (rec baseπ loopπ mulπ groupoidπ) (loop x) = loopπ x

  attribute [irreducible] K1

  instance : dotted (K1 G) := ⟨base⟩

  def KΩ.mul : Ω¹(K1 G) → Ω¹(K1 G) → Ω¹(K1 G) := λ p q, p ⬝ q
  def KΩ.one : Ω¹(K1 G)                       := idp base
  def KΩ.inv : Ω¹(K1 G) → Ω¹(K1 G)            := Id.inv

  noncomputable def KΩ (G : Pregroup) : Pregroup :=
  @Pregroup.intro (Ω¹(K1 G)) (grpd _ _) KΩ.mul KΩ.inv KΩ.one

  noncomputable instance KΩ.semigroup (G : Pregroup) : semigroup (KΩ G).magma :=
  ⟨begin intros p q r; symmetry; apply Id.assoc end⟩

  noncomputable instance KΩ.monoid (G : Pregroup) : monoid (KΩ G).premonoid :=
  begin
    apply monoid.mk; exact KΩ.semigroup G;
    intro p; apply Id.reflLeft; apply Id.reflRight
  end

  noncomputable instance KΩ.group (G : Pregroup) : group (KΩ G) :=
  begin apply group.mk; exact KΩ.monoid G; apply Id.invComp end

  noncomputable def homomorphism [group G] : G ⤳ KΩ G :=
  Group.mkhomo loop loop.mul

  noncomputable def loop.one [group G] : @Id Ω¹(K1 G) (loop G.e) (idp base) :=
  Group.homoUnit homomorphism

  noncomputable def loop.inv [group G] : Π p, loop (G.ι p) = (loop p)⁻¹ :=
  Group.homoInv homomorphism

  noncomputable hott def family
    (baseπ : Type u)
    (loopπ : G.carrier → baseπ = baseπ)
    (mulπ  : Π x y, loopπ (x * y) = loopπ x ⬝ loopπ y)
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

  noncomputable hott def code' [group G] : K1 G → (0-Type) :=
  begin
    fapply family; exact G.carrier;
    { intro x; apply ua; existsi (G.φ · x); apply Prod.mk <;>
      existsi (G.φ · (G.ι x)) <;> intro y <;> change _ * _ * _ = _;
      symmetry; apply Group.cancelRight;
      symmetry; apply Group.cancelLeft };
    { intros x y; symmetry; transitivity;
      { symmetry; apply ua.uaTrans };
      apply Id.map ua; fapply Sigma.prod;
      { apply Theorems.funext; intro; apply G.mulAssoc };
      { apply biinvProp } };
    apply G.hset
  end

  hott def code [group G] (x : K1 G) := (code' x).fst

  noncomputable hott def code.hset [group G] (z : K1 G) : hset (code z) :=
  begin
    induction z; apply G.hset; apply setIsProp;
    { apply propIsSet; apply setIsProp };
    { apply oneEqvGroupoid.forward;
      apply propIsNType _ 0;
      apply setIsProp }
  end

  noncomputable hott def hsetBase [p : group G] : hset (@code G p base) := code.hset base

  hott def encode [group G] : Π (z : K1 G), base = z → code z :=
  λ z p, Equiv.transport code p G.e

  noncomputable hott def decode [group G] (z : K1 G) : code z → base = z :=
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
      transitivity; apply Id.map; apply recβrule;
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

  noncomputable hott def encodeDecode [group G] (z : K1 G) :
    Π (p : code z), encode z (decode z p) = p :=
  begin
    induction z;
    { intro (x : G.carrier); change encode base (loop x) = _;
      transitivity; apply Equiv.transportToTransportconst;
      transitivity; apply Id.map (Equiv.transportconst · G.e);
      transitivity; apply Equiv.mapOverComp;
      transitivity; apply Id.map; apply recβrule;
      apply Sigma.mapFstOverProd; transitivity;
      apply ua.transportRule; apply G.oneMul };
    { apply Theorems.funext; intro; apply hsetBase };
    { apply propIsSet; apply piProp; intro; apply hsetBase };
    { apply oneEqvGroupoid.forward; apply propIsNType _ 0;
      intros p q; apply Theorems.funext; intro; apply code.hset }
  end

  noncomputable hott def decodeEncode [group G] :
    Π (z : K1 G) (p : base = z), decode z (encode z p) = p :=
  begin intros z p; induction p; apply loop.one end

  noncomputable hott def univ [p : group G] : G ≅ KΩ G :=
  begin
    fapply Group.mkiso; exact loop;
    { intros x y; apply loop.mul };
    apply Prod.mk <;> existsi encode base;
    apply encodeDecode; apply decodeEncode
  end
end K1

end GroundZero.Algebra