import GroundZero.Algebra.Group.Basic
import GroundZero.HITs.Suspension
import GroundZero.HITs.Trunc

open GroundZero.Theorems.Functions GroundZero.Theorems.Equiv
open GroundZero.Types.Equiv (idtoeqv apd)
open GroundZero.Types.Id (isPointed ap)
open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.Algebra
universe u v

private def K1.aux := Opaque 𝟏

attribute [nothott] K1.aux

@[hottAxiom] def K1 (G : Group) := K1.aux

namespace K1
  variable {G : Group}

  def base : K1 G := Opaque.intro ★

  opaque grpd : groupoid (K1 G) :=
  λ _ _ _ _, λ (idp _), λ (idp _), idp _

  opaque loop (g : G.carrier) : @Id (K1 G) base base := idp base

  opaque loop.mul (x y : G.carrier) : loop (G.φ x y) = loop x ⬝ loop y :=
  trustCoherence

  def ind {C : K1 G → Type v} (baseπ : C base) (loopπ : Π (x : G.carrier), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : G.carrier), loopπ (G.φ x y) =[λ p, baseπ =[p] baseπ, loop.mul x y] loopπ x ⬝′ loopπ y)
    (groupoidπ : Π x, groupoid (C x)) : Π x, C x :=
  λ x, Quot.withUseOf (loopπ, mulπ, groupoidπ) (Opaque.ind (λ ★, baseπ) x) x

  attribute [eliminator] ind

  def rec {C : Type v} (baseπ : C) (loopπ : G.carrier → baseπ = baseπ)
    (mulπ : Π x y, loopπ (G.φ x y) = loopπ x ⬝ loopπ y)
    (groupoidπ : groupoid C) : K1 G → C :=
  λ x, Quot.withUseOf (loopπ, mulπ, groupoidπ) (Opaque.elim (λ ★, baseπ) x) x

  opaque indβrule {C : K1 G → Type v} (baseπ : C base) (loopπ : Π (x : G.carrier), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : G.carrier), loopπ (G.φ x y) =[λ p, baseπ =[p] baseπ, loop.mul x y] loopπ x ⬝′ loopπ y)
    (groupoidπ : Π x, groupoid (C x)) : Π x, apd (ind baseπ loopπ mulπ groupoidπ) (loop x) = loopπ x :=
  λ _, trustCoherence

  opaque recβrule {C : Type v} (baseπ : C) (loopπ : G.carrier → baseπ = baseπ)
    (mulπ : Π x y, loopπ (G.φ x y) = loopπ x ⬝ loopπ y) (groupoidπ : groupoid C) :
    Π x, ap (rec baseπ loopπ mulπ groupoidπ) (loop x) = loopπ x :=
  λ _, trustCoherence

  attribute [hottAxiom] K1 base grpd loop loop.mul rec ind recβrule indβrule

  attribute [irreducible] K1

  instance : isPointed (K1 G) := ⟨base⟩

  def KΩ.mul : Ω¹(K1 G) → Ω¹(K1 G) → Ω¹(K1 G) := λ p q, p ⬝ q
  def KΩ.one : Ω¹(K1 G)                       := idp base
  def KΩ.inv : Ω¹(K1 G) → Ω¹(K1 G)            := Id.inv

  hott def KΩ (G : Group) : Group :=
  @Group.intro (Ω¹(K1 G)) (grpd _ _) KΩ.mul KΩ.inv KΩ.one
    (λ _ _ _, Id.inv (Id.assoc _ _ _))
    Id.lid Id.rid Id.invComp

  hott def homomorphism : Group.Hom G (KΩ G) :=
  Group.mkhomo loop loop.mul

  hott def loop.one : @Id Ω¹(K1 G) (loop G.e) (idp base) :=
  Group.homoUnit homomorphism

  hott def loop.inv : Π p, loop (G.ι p) = (loop p)⁻¹ :=
  Group.homoInv homomorphism

  hott def family (baseπ : Type u)
    (loopπ : G.carrier → baseπ = baseπ)
    (mulπ  : Π x y, loopπ (G.φ x y) = loopπ x ⬝ loopπ y)
    (setπ  : hset baseπ) : K1 G → 0-Type :=
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

  hott def code' : K1 G → 0-Type :=
  begin
    fapply family; exact G.carrier;
    { intro x; apply ua; existsi (G.φ · x); apply Prod.mk <;>
      existsi (G.φ · (G.ι x)) <;> intro y <;> change G.φ (G.φ _ _) _ = _;
      symmetry; apply Group.cancelRight;
      symmetry; apply Group.cancelLeft };
    { intros x y; symmetry; transitivity;
      { symmetry; apply uacom };
      apply ap ua; fapply Sigma.prod;
      { apply Theorems.funext; intro; apply G.mulAssoc };
      { apply biinvProp } };
    apply G.hset
  end

  hott def code (x : K1 G) := (code' x).fst

  hott def code.hset (z : K1 G) : hset (code z) :=
  begin
    induction z; apply G.hset; apply setIsProp;
    { apply propIsSet; apply setIsProp };
    { apply oneEqvGroupoid.forward;
      apply propIsNType _ 0;
      apply setIsProp }
  end

  hott def hsetBase : hset (@code G base) := code.hset base

  hott def encode : Π (z : K1 G), base = z → code z :=
  λ z p, Equiv.transport code p G.e

  hott def decode (z : K1 G) : code z → base = z :=
  begin
    induction z; exact loop;
    case loopπ x =>
    { change _ = _; transitivity; apply Equiv.transportCharacterization;
      apply Theorems.funext; intro y; transitivity;
      apply ap (λ p, Equiv.transport (λ x, base = x) (loop x) (loop p));
      transitivity; apply Equiv.transportToTransportconst;
      transitivity; apply ap (Equiv.transportconst · y);
      transitivity; apply Id.mapInv; apply ap;
      transitivity; apply Equiv.mapOverComp;
      transitivity; apply ap; unfold code'; apply recβrule;
      apply Sigma.mapFstOverProd; apply uaβrev;
      transitivity; apply Equiv.transportOverInvContrMap;
      transitivity; apply ap; apply Equiv.idmap;
      transitivity; apply ap (· ⬝ loop x); apply loop.mul;
      transitivity; symmetry; apply Id.assoc;
      transitivity; apply ap; apply ap (· ⬝ loop x); apply loop.inv;
      transitivity; apply ap; apply Id.invComp; apply Id.rid };
    { apply zeroEqvSet.forward; apply piRespectsNType 0;
      intro; apply zeroEqvSet.left; apply grpd };
    { apply oneEqvGroupoid.forward;
      apply piRespectsNType 1; intro;
      apply hlevel.cumulative 0;
      apply zeroEqvSet.left; apply grpd }
  end

  hott lemma encodeDecode (z : K1 G) : Π (p : code z), encode z (decode z p) = p :=
  begin
    induction z;
    { intro (x : G.carrier); change encode base (loop x) = _;
      transitivity; apply Equiv.transportToTransportconst;
      transitivity; apply ap (Equiv.transportconst · G.e);
      transitivity; apply Equiv.mapOverComp;
      transitivity; apply ap; unfold code'; apply recβrule;
      apply Sigma.mapFstOverProd; transitivity;
      apply uaβ; apply G.oneMul };
    { apply Theorems.funext; intro; apply hsetBase };
    { apply propIsSet; apply piProp; intro; apply hsetBase };
    { apply oneEqvGroupoid.forward; apply propIsNType _ 0;
      intros p q; apply Theorems.funext; intro; apply code.hset }
  end

  hott lemma decodeEncode : Π (z : K1 G) (p : base = z), decode z (encode z p) = p :=
  begin intros z p; induction p; apply loop.one end

  hott theorem univ : G ≅ KΩ G :=
  begin
    fapply Group.mkiso; exact loop;
    { intros x y; apply loop.mul };
    apply Prod.mk <;> existsi encode base;
    { intro; apply encodeDecode };
    { apply decodeEncode }
  end
end K1

hott def ItS (A : Type) : ℕ → Type
|      0     => A
| Nat.succ n => ∑ (ItS A n)

open GroundZero.HITs (Trunc)

hott def K (G : Group) (n : ℕ) :=
Trunc (hlevel.ofNat (n + 1)) (ItS (K1 G) n)

end GroundZero.Algebra
