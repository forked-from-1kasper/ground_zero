import GroundZero.Theorems.Functions
import GroundZero.HITs.Circle

open GroundZero.Theorems.Functions (injective)
open GroundZero.Theorems (funext)
open GroundZero.Types.Equiv
open GroundZero.HITs.Circle
open GroundZero.Structures
open GroundZero.Types.Id
open GroundZero.Types
open GroundZero

/-
  Homotopical Reals R.
  * HoTT 8.1.5
-/

namespace GroundZero.HITs
universe u v w

inductive Reals.rel : ℤ → ℤ → Type
| glue (x : ℤ) : rel x (Integer.succ x)
hott def Reals := Graph Reals.rel

hott def R := Reals

namespace Reals
  hott def elem : ℤ → R := Graph.elem
  hott def glue (z : ℤ) : elem z = elem (Integer.succ z) :=
  Graph.line (rel.glue z)

  hott def indρ {C : R → Type u} (cz : Π x, C (elem x))
    (sz : Π z, cz z =[glue z] cz (Integer.succ z))
    (x y : ℤ) (ρ : rel x y) : cz x =[Graph.line ρ] cz y :=
  begin induction ρ using rel.casesOn; apply sz end

  hott def ind {C : R → Type u} (cz : Π x, C (elem x))
    (sz : Π z, cz z =[glue z] cz (Integer.succ z)) (u : R) : C u :=
  Graph.ind cz (indρ cz sz) u

  attribute [eliminator] ind

  noncomputable hott def indβrule {C : R → Type u}
    (cz : Π x, C (elem x)) (sz : Π z, cz z =[glue z] cz (Integer.succ z))
    (z : ℤ) : Equiv.apd (ind cz sz) (glue z) = sz z :=
  @Graph.indβrule _ _ C cz (indρ cz sz) _ _ (rel.glue z)

  hott def rec {A : Type u} (cz : ℤ → A)
    (sz : Π z, cz z = cz (Integer.succ z)) : R → A :=
  ind cz (λ x, Equiv.pathoverOfEq (glue x) (sz x))

  noncomputable hott def recβrule {A : Type u} (cz : ℤ → A)
    (sz : Π z, cz z = cz (Integer.succ z)) (z : ℤ) :
    Id.map (rec cz sz) (glue z) = sz z := 
  begin
    apply Equiv.pathoverOfEqInj (glue z); transitivity;
    symmetry; apply Equiv.apdOverConstantFamily;
    transitivity; apply indβrule; reflexivity
  end

  hott def positive : Π n, elem 0 = elem (Integer.pos n)
  | Nat.zero   => idp (elem 0)
  | Nat.succ n => positive n ⬝ glue (Integer.pos n)

  hott def negative : Π n, elem 0 = elem (Integer.neg n)
  | Nat.zero   => (glue (Integer.neg 0))⁻¹
  | Nat.succ n => negative n ⬝ (glue (Integer.neg (n + 1)))⁻¹

  hott def center : Π z, elem 0 = elem z
  | Integer.pos n => positive n
  | Integer.neg n => negative n

  hott def vect (u v : ℤ) : elem u = elem v :=
  (center u)⁻¹ ⬝ center v

  hott def contractible : contr R :=
  ⟨elem 0, @ind (elem 0 = ·) center (begin
    intro z; change _ = _; transitivity;
    apply Equiv.transportComposition; match z with
    | Integer.pos _ => reflexivity;
    | Integer.neg n => _;
    induction n using Nat.casesOn; apply Id.invComp;
    { transitivity; symmetry; apply Id.assoc;
      transitivity; apply Id.map; apply Id.invComp;
      apply Id.reflRight }
  end)⟩

  hott def dist : Π (u v : R), u = v :=
  Structures.contrImplProp contractible

  hott def lift (f : ℤ → ℤ) : R → R :=
  rec (elem ∘ f) (λ _, dist _ _)

  hott def operator (f : ℤ → ℤ → ℤ) : R → R → R :=
  rec (lift ∘ f) (λ _, Theorems.funext (λ _, dist _ _))

  instance (n : ℕ) : OfNat R n := ⟨elem (Integer.pos n)⟩

  section
    variable {A : Type⁎} (H : prop A.space)
    variable (φ : Map⁎ A ⟨S¹, base⟩)

    hott def helixOverHomo (x : A.1) : helix (φ.ap x) = ℤ :=
    begin
      transitivity; apply map (helix ∘ φ.ap);
      apply H x A.point; change _ = helix base;
      apply map helix; apply φ.id
    end

    noncomputable hott def fibOfHomo (x : S¹) := calc
      fib φ.ap x ≃ Σ (z : A.1), φ.ap z = x       : Equiv.ideqv (fib φ.ap x)
             ... = Σ (z : A.1), φ.ap A.point = x : Id.map Sigma (funext (λ z, Id.map (φ.ap · = x) (H z A.point)))
             ... = Σ (z : A.1), base = x         : Id.map Sigma (funext (λ _, Id.map (· = x) φ.id))
             ... = Σ (z : A.1), helix x          : Id.map Sigma (funext (λ _, GroundZero.ua (Circle.family x)))
             ... ≃ A.1 × (helix x)               : Sigma.const A.1 (helix x)
             ... ≃ 𝟏 × (helix x)                 : ua.productEquiv₃ (contrEquivUnit.{_, 0} ⟨A.point, H A.point⟩) (Equiv.ideqv (helix x))
             ... ≃ helix x                       : prodUnitEquiv (helix x)

    noncomputable hott def kerOfHomo : fib φ.ap base ≃ ℤ :=
    fibOfHomo H φ base
  end

  /-
            ≃
       S¹ ←–––– R/τℤ
       ↑          ↑
   eⁱ⁻ |          |
       |          |
       R ════════ R
  -/
  hott def cis : R → S¹ := rec (λ _, base) (λ _, loop)

  noncomputable hott def Euler : fib cis base ≃ ℤ :=
  @kerOfHomo ⟨R, 0⟩ dist ⟨cis, idp base⟩

  -- Another (more tricky) proof, but it does not use R contractibility
  noncomputable hott def helixOverCis (x : R) : helix (cis x) = ℤ :=
  begin
    induction x;
    case cz x => { apply (Integer.shift x)⁻¹ };
    case sz z => {
      change _ = _; let p := Integer.shift z; apply calc
            Equiv.transport (λ x, helix (cis x) = ℤ) (glue z) (Integer.shift z)⁻¹
          = @Id.map R Type _ _ (helix ∘ cis) (glue z)⁻¹ ⬝ (Integer.shift z)⁻¹ :
        Equiv.transportOverContrMap _ _ _
      ... = (Id.map (helix ∘ cis) (glue z))⁻¹ ⬝ (Integer.shift z)⁻¹ :
        Id.map (· ⬝ p⁻¹) (Id.mapInv _ _)
      ... = (Id.map helix (Id.map cis (glue z)))⁻¹ ⬝ (Integer.shift z)⁻¹ :
        Id.map (·⁻¹ ⬝ p⁻¹) (Equiv.mapOverComp _ _ _)
      ... = (Id.map helix loop)⁻¹ ⬝ (Integer.shift z)⁻¹ :
        begin apply Id.map (·⁻¹ ⬝ p⁻¹); apply Id.map; apply recβrule end
      ... = Integer.succPath⁻¹ ⬝ (Integer.shift z)⁻¹ :
        begin apply Id.map (·⁻¹ ⬝ p⁻¹); apply Circle.recβrule₂ end
      ... = (Integer.shift z ⬝ Integer.succPath)⁻¹ :
        (Id.explodeInv _ _)⁻¹
      ... = (Integer.shift (Integer.succ z))⁻¹ :
        Id.map _ (Integer.shiftComp _)
    }
  end

  hott def phiEqvBaseImplContr {A : Type u} {x : A}
    (H : Π (φ : A → S¹), φ x = base) : contr S¹ :=
  ⟨base, λ y, (H (λ _, y))⁻¹⟩

  hott def phiNeqBaseImplFalse {A : Type u} {x : A} (φ : A → S¹) : ¬¬(φ x = base) :=
  begin induction φ x; intro p; apply p; reflexivity; apply implProp; apply emptyIsProp end

  hott def lemInfImplDnegInf (H : LEM∞) {A : Type u} (G : ¬¬A) : A :=
  match H A with
  | Sum.inl x => x
  | Sum.inr y => Proto.Empty.elim (G y)

  noncomputable hott def circleNotHset : ¬(hset S¹) :=
  begin intro H; apply Circle.loopNeqRefl; apply H end

  noncomputable hott def lemInfDisproved : ¬LEM∞ :=
  begin
    intro H; apply circleNotHset; apply propIsSet; apply contrImplProp;
    apply phiEqvBaseImplContr; intro φ; apply lemInfImplDnegInf H;
    apply phiNeqBaseImplFalse φ; exact R; exact 0
  end

  noncomputable hott def cisFamily : (R → S¹) ≃ S¹ :=
  @transport Type (λ A, (A → S¹) ≃ S¹) 𝟏 R
    (ua (contrEquivUnit contractible))⁻¹ cozeroMorphismEqv

  hott def countable (A : Type u) :=
  ∥(Σ (f : A → ℕ), injective f)∥

  noncomputable hott def circleUncountable : ¬(countable S¹) :=
  begin
    fapply HITs.Merely.rec; apply emptyIsProp;
    intro ⟨f, H⟩; apply circleNotHset;
    apply propIsSet; intros x y; apply H;
    induction x; induction y; reflexivity;
    apply Theorems.Nat.natIsSet;
    apply Theorems.Nat.natIsSet
  end
end Reals

end GroundZero.HITs
