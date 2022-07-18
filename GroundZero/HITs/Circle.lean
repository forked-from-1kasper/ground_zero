import GroundZero.HITs.Suspension
import GroundZero.Theorems.Equiv
import GroundZero.Types.Integer

open GroundZero.HITs.Interval
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types.Id
open GroundZero.Types

/-
  Circle S¹ as Higher Inductive Type.
  * HoTT 6.4

  π₁(S¹) = ℤ proof.
  * HoTT 8.1
-/

namespace GroundZero
namespace HITs

universe u v w

hott def suspEmpty : ∑ 𝟎 ≃ 𝟐 :=
let f : ∑ 𝟎 → 𝟐 :=
Suspension.rec false true Proto.Empty.elim
let g : 𝟐 → ∑ 𝟎 :=
λ | false => Suspension.north
  | true  => Suspension.south;
begin
  existsi f; apply Prod.mk <;> existsi g;
  { intro z; induction z; reflexivity; reflexivity;
    apply Proto.Empty.elim; assumption };
  { intro b; induction b using Bool.casesOn <;> reflexivity }
end

namespace Loop
  variable {A : Type u} {a : A}

  def pos (p : a = a) : ℕ → a = a
  | Nat.zero   => idp a
  | Nat.succ n => pos p n ⬝ p

  def neg (p : a = a) : ℕ → a = a
  | Nat.zero   => p⁻¹
  | Nat.succ n => neg p n ⬝ p⁻¹

  def power (p : a = a) : ℤ → a = a
  | Integer.pos n => pos p n
  | Integer.neg n => neg p n

  hott def powerComp (p : a = a) : Π z, power p z ⬝ p = power p (Integer.succ z)
  | Integer.neg Nat.zero     => Id.invComp _
  | Integer.neg (Nat.succ n) => (Id.assoc _ _ _)⁻¹ ⬝ Id.map (neg p n ⬝ ·) (Id.invComp _) ⬝ Id.reflRight _
  | Integer.pos _            => idp _

  hott def powerCompPred (p : a = a) : Π z, power p z ⬝ p⁻¹ = power p (Integer.pred z)
  | Integer.neg _            => idp _
  | Integer.pos Nat.zero     => idp _
  | Integer.pos (Nat.succ n) => (Id.assoc _ _ _)⁻¹ ⬝ Id.map (pos p n ⬝ ·) (Id.compInv _) ⬝ Id.reflRight _

  hott def compPowerPos (p : a = a) : Π n, p ⬝ power p (Integer.pos n) = power p (Integer.succ (Integer.pos n))
  | Nat.zero   => Id.reflRight _
  | Nat.succ n => Id.assoc _ _ _ ⬝ Id.map (· ⬝ p) (compPowerPos p n)

  hott def compPowerNeg (p : a = a) : Π n, p ⬝ power p (Integer.neg n) = power p (Integer.succ (Integer.neg n))
  | Nat.zero   => Id.compInv _
  | Nat.succ n => begin
    transitivity; apply Id.assoc;
    symmetry; apply Equiv.invCompRewrite;
    symmetry; transitivity; apply compPowerNeg p n;
    symmetry; apply powerComp
  end

  hott def compPower (p : a = a) : Π z, p ⬝ power p z = power p (Integer.succ z)
  | Integer.neg n => compPowerNeg p n
  | Integer.pos m => compPowerPos p m

  hott def compPowerPred (p : a = a) : Π z, p⁻¹ ⬝ power p z = power p (Integer.pred z)
  | Integer.neg Nat.zero     => idp _
  | Integer.neg (Nat.succ n) => begin apply Equiv.rewriteComp; symmetry; apply compPower end
  | Integer.pos Nat.zero     => Id.reflRight _
  | Integer.pos (Nat.succ n) => begin apply Equiv.rewriteComp; symmetry; apply compPower end

  hott def compPowerComm (p : a = a) (z : ℤ) :
    p ⬝ power p z = power p z ⬝ p :=
  compPower p z ⬝ (powerComp p z)⁻¹

  hott def invCompPowerComm (p : a = a) (z : ℤ) :
    p⁻¹ ⬝ power p z = power p z ⬝ p⁻¹ :=
  compPowerPred p z ⬝ (powerCompPred p z)⁻¹

  hott def powerComm (p : a = a) (x y : ℤ) : power p x ⬝ power p y = power p y ⬝ power p x :=
  begin
    fapply @Integer.indsp (λ x, Π y, power p x ⬝ power p y = power p y ⬝ power p x) _ _ _ x <;> clear x;
    { intro y; symmetry; apply Id.reflRight };
    { intros x ih y; transitivity; apply Id.map (· ⬝ power p y);
      symmetry; apply compPower;
      transitivity; symmetry; apply Id.assoc;
      transitivity; apply Id.map; apply ih;
      transitivity; apply Id.assoc;
      transitivity; apply Id.map (· ⬝ power p x); apply compPowerComm;
      transitivity; symmetry; apply Id.assoc;
      apply Id.map; apply compPower };
    { intros x ih y; transitivity; apply Id.map (· ⬝ power p y);
      symmetry; apply compPowerPred;
      transitivity; symmetry; apply Id.assoc;
      transitivity; apply Id.map; apply ih;
      transitivity; apply Id.assoc;
      transitivity; apply Id.map (· ⬝ power p x);
      apply invCompPowerComm;
      transitivity; symmetry; apply Id.assoc;
      apply Id.map; apply compPowerPred }
  end
end Loop

hott def S : ℕ → Type
| Nat.zero   => 𝟐
| Nat.succ n => ∑ (S n)

def S.lift : Π n, S n → S (n + 1)
| Nat.zero,   false => Suspension.north
| Nat.zero,   true  => Suspension.south
| Nat.succ _, z     => Suspension.rec Suspension.north Suspension.south (λ _, Suspension.merid z) z

macro:max "S" n:superscript : term => do `(GroundZero.HITs.S $(← Meta.Notation.parseSuperscript n))
instance (n : ℕ) : Id.dotted Sⁿ :=
⟨match n with
 | Nat.zero   => false
 | Nat.succ _ => Suspension.north⟩

macro:max "S" : term => `(GroundZero.HITs.S)

def Circle := S¹

namespace Circle
  -- https://github.com/leanprover/lean2/blob/master/hott/homotopy/Circle.hlean

  def base₁ : S¹ := Suspension.north
  def base₂ : S¹ := Suspension.south

  def seg₁ : base₁ = base₂ := Suspension.merid false
  def seg₂ : base₁ = base₂ := Suspension.merid true

  hott def ind₂ {B : S¹ → Type u} (b₁ : B base₁) (b₂ : B base₂)
    (ℓ₁ : b₁ =[seg₁] b₂) (ℓ₂ : b₁ =[seg₂] b₂) : Π x, B x :=
  Suspension.ind b₁ b₂ (λ | false => ℓ₁ | true => ℓ₂)

  def base : S¹ := base₁
  def loop : base = base := seg₂ ⬝ seg₁⁻¹

  hott def rec {B : Type u} (b : B) (ℓ : b = b) : S¹ → B :=
  Suspension.rec b b (λ | false => idp b | true => ℓ)

  hott def recβrule₁ {B : Type u} (b : B) (ℓ : b = b) : rec b ℓ base = b :=
  idp b

  -- why this doesn’t require “noncomputable” attribute as it was in Lean 3?
  -- looks pretty strange
  hott def recβrule₂ {B : Type u} (b : B) (ℓ : b = b) := calc
          Id.map (rec b ℓ) loop
        = Id.map (rec b ℓ) seg₂ ⬝ Id.map (rec b ℓ) seg₁⁻¹   : Equiv.mapFunctoriality _
    ... = Id.map (rec b ℓ) seg₂ ⬝ (Id.map (rec b ℓ) seg₁)⁻¹ : Id.map (_ ⬝ ·) (Id.mapInv _ _)
    ... = ℓ ⬝ Id.refl⁻¹                                     : bimap (· ⬝ ·⁻¹) (Suspension.recβrule _ _ _ _) (Suspension.recβrule _ _ _ _)
    ... = ℓ                                                 : Id.reflRight _

  hott def recβrule₃ {B : Type u} (b : B) (ℓ : b = b) := calc
            Id.map (rec b ℓ) loop⁻¹
          = (Id.map (rec b ℓ) loop)⁻¹ : Id.mapInv _ _
      ... = ℓ⁻¹                       : Id.map Id.inv (recβrule₂ _ _)

  hott def ind {B : S¹ → Type u} (b : B base) (ℓ : b =[loop] b) : Π (x : S¹), B x :=
  ind₂ b (Equiv.subst seg₁ b) Id.refl (depPathTransSymm ℓ)

  attribute [eliminator] ind

  hott def indβrule₁ {B : S¹ → Type u} (b : B base) (ℓ : b =[loop] b) : ind b ℓ base = b :=
  idp b

  hott def indβrule₂ {B : S¹ → Type u} (b : B base) (ℓ : b =[loop] b) : apd (ind b ℓ) loop = ℓ :=
  begin
    dsimp [ind, ind₂];
    transitivity; apply apdFunctoriality;
    transitivity; apply bimap depTrans; apply Suspension.indβrule;
    transitivity; apply apdInv; apply Id.map;
    apply Suspension.indβrule; apply depPathTransSymmCoh
  end

  hott def indΩ {B : S¹ → Type u} (b : B base) (H : Π x, prop (B x)) : Π x, B x :=
  begin fapply ind; exact b; apply H end

  noncomputable hott def loopEqReflImplsUip {A : Type u} (H : loop = idp base) : K A :=
  begin
    intros a p; transitivity;
    symmetry; apply Circle.recβrule₂ a p;
    change _ = Id.map (rec a p) (idp _);
    apply Id.map; apply H
  end

  noncomputable hott def loopNeqRefl : ¬(loop = idp base) :=
  begin
    intro H; apply ua.universeNotASet;
    intros A B p q; apply (KIffSet Type).left;
    apply loopEqReflImplsUip; assumption
  end

  namespace map
    def trivial    : S¹ → S¹ := rec base (idp base)
    def nontrivial : S¹ → S¹ := rec base loop

    noncomputable hott def trivialNotHmtpy : ¬(trivial = id) :=
    begin
      intro p; apply loopNeqRefl; transitivity; symmetry; apply idmap;
      apply transport (λ f, Id.map f loop = idp (f base)) p; apply Circle.recβrule₂
    end

    noncomputable hott def trivialHmtpy : trivial ~ (λ _, base) :=
    begin
      intro x; induction x; reflexivity; apply Id.trans; apply transportOverContrMap;
      transitivity; apply Id.map (· ⬝ idp base); transitivity; apply Id.mapInv;
      apply Id.map; apply recβrule₂; reflexivity
    end

    noncomputable hott def nontrivialHmtpy : nontrivial ~ id :=
    begin
      intro x; induction x; reflexivity;
      apply Id.trans; apply transportOverInvolution;
      transitivity; apply Id.map (· ⬝ idp base ⬝ loop);
      transitivity; apply Id.mapInv; apply Id.map; apply recβrule₂;
      transitivity; symmetry; apply Id.assoc; apply Id.invComp
    end

    noncomputable hott def nontrivialNotHmtpy : ¬(nontrivial = (λ _, base)) :=
    λ p, trivialNotHmtpy (Theorems.funext trivialHmtpy ⬝ p⁻¹ ⬝
                          Theorems.funext nontrivialHmtpy)
  end map

  def succ (l : Ω¹(S¹)) : Ω¹(S¹) := l ⬝ loop
  def pred (l : Ω¹(S¹)) : Ω¹(S¹) := l ⬝ loop⁻¹

  def zero   := idp base
  def one    := succ zero
  def two    := succ one
  def three  := succ two
  def fourth := succ three

  hott def helix : S¹ → Type :=
  rec ℤ (ua Integer.succEquiv)

  def power : ℤ → Ω¹(S¹) := Loop.power loop

  hott def encode (x : S¹) (p : base = x) : helix x :=
  transport helix p (Integer.pos 0)

  example : power 2 = loop ⬝ loop :=
  by reflexivity

  hott def winding : base = base → ℤ := encode base

  noncomputable hott def transportThere (x : ℤ) := calc
          transport helix loop x
        = transportconst (Id.map helix loop) x    : Equiv.transportComp id helix loop x
    ... = transportconst (ua Integer.succEquiv) x : Id.map (transportconst · x) (recβrule₂ _ _)
    ... = Integer.succ x                          : ua.transportRule _ _

  noncomputable hott def transportBack (x : ℤ) := calc
           transport helix loop⁻¹ x
         = transportconst (Id.map helix loop⁻¹) x    : Equiv.transportComp id helix loop⁻¹ x
     ... = transportconst (Id.map helix loop)⁻¹ x    : Id.map (transportconst · x) (Id.mapInv _ _)
     ... = transportconst (ua Integer.succEquiv)⁻¹ x : Id.map (transportconst ·⁻¹ x) (recβrule₂ _ _)
     ... = Integer.pred x                            : ua.transportInvRule _ _

  noncomputable hott def decode (x : S¹) : helix x → base = x :=
  begin
    induction x; exact power; apply Theorems.funext; intro x;
    transitivity; apply Homotopy.Id (transportCharacterization power loop) x;
    transitivity; apply transportComposition;
    transitivity; apply Id.map (power · ⬝ loop); apply transportBack;
    transitivity; apply Id.map (· ⬝ loop);
    transitivity; symmetry; apply Loop.compPowerPred; apply Loop.invCompPowerComm;
    apply Id.cancelInvComp
  end

  noncomputable hott def decodeEncode (x : S¹) (p : base = x) : decode x (encode x p) = p :=
  begin induction p; reflexivity end

  noncomputable hott def powerOfWinding : power ∘ winding ~ id :=
  decodeEncode base

  noncomputable hott def windingPos : Π n, winding (power (Integer.pos n)) = Integer.pos n
  | Nat.zero   => idp _
  | Nat.succ n => substOverPathComp _ _ _ ⬝ transportThere _ ⬝ Id.map _ (windingPos n)

  noncomputable hott def windingNeg : Π n, winding (power (Integer.neg n)) = Integer.neg n
  | Nat.zero   => transportBack _
  | Nat.succ n => substOverPathComp _ _ _ ⬝ transportBack _ ⬝ Id.map _ (windingNeg n)

  noncomputable hott def windingPower : Π z, winding (power z) = z
  | Integer.neg n => windingNeg n
  | Integer.pos n => windingPos n

  noncomputable hott def encodeDecode (x : S¹) : Π c, encode x (decode x c) = c :=
  begin induction x; intro c; apply windingPower; apply Theorems.funext; intro z; apply Integer.set end

  noncomputable hott def family (x : S¹) : (base = x) ≃ helix x :=
  ⟨encode x, (⟨decode x, decodeEncode x⟩, ⟨decode x, encodeDecode x⟩)⟩

  noncomputable hott def fundamentalGroup : Ω¹(S¹) = ℤ := ua (family base)

  noncomputable hott def loopHset : hset (base = base) :=
  transport hset fundamentalGroup⁻¹ Integer.set

  noncomputable example : winding (loop ⬝ loop) = 2 := windingPower 2
  noncomputable example : winding loop = 1          := windingPower 1
  noncomputable example : winding loop⁻¹ = -1       := windingPower (-1)

  hott def rot : Π (x : S¹), x = x :=
  Circle.ind Circle.loop (begin
    apply Id.trans; apply transportInvCompComp; change _ = idp _ ⬝ loop;
    apply Id.map (· ⬝ loop); apply Id.invComp
  end)

  def μₑ : S¹ → S¹ ≃ S¹ :=
  Circle.rec (ideqv S¹) (Sigma.prod (Theorems.funext rot) (Theorems.Equiv.biinvProp _ _ _))

  def μ (x : S¹) : S¹ → S¹ := (μₑ x).forward

  noncomputable hott def μLoop : Id.map μ loop = Theorems.funext rot :=
  begin
    transitivity; apply mapOverComp;
    transitivity; apply Id.map; apply recβrule₂;
    apply Sigma.mapFstOverProd
  end

  hott def inv : S¹ → S¹ := Circle.rec base loop⁻¹

  noncomputable hott def invInv (x : S¹) : inv (inv x) = x :=
  let invₚ := @Id.map S¹ S¹ base base (inv ∘ inv);
  begin
    induction x; reflexivity; apply calc
              transport (λ x, inv (inv x) = x) loop Id.refl
            = invₚ loop⁻¹ ⬝ Id.refl ⬝ loop          : transportOverInvolution _ _ _
        ... = invₚ loop⁻¹ ⬝ (Id.refl ⬝ loop)        : (Id.assoc _ _ _)⁻¹
        ... = Id.map inv (Id.map inv loop⁻¹) ⬝ loop : Id.map (· ⬝ loop) (mapOverComp _ _ _)
        ... = Id.map inv (Id.map inv loop)⁻¹ ⬝ loop : Id.map (Id.map inv · ⬝ loop) (Id.mapInv inv loop)
        ... = Id.map inv loop⁻¹⁻¹ ⬝ loop            : @Id.map Ω¹(S¹) _ _ _ (Id.map inv ·⁻¹ ⬝ loop) (Circle.recβrule₂ base loop⁻¹)
        ... = Id.map inv loop ⬝ loop                : @Id.map Ω¹(S¹) _ _ _ (Id.map inv · ⬝ loop) (Id.invInv _)
        ... = loop⁻¹ ⬝ loop                         : Id.map (· ⬝ loop) (Circle.recβrule₂ _ _)
        ... = idp base                              : Id.invComp _
  end

  hott def unitLeft (x : S¹) : μ base x = x := idp x

  hott def μRight : Id.map (μ base) loop = loop := Equiv.idmap _

  noncomputable hott def μLeft := calc
          Id.map (μ · base) loop
        = happly (Id.map μ loop) base         : Interval.mapHapply _ _
    ... = (happly ∘ Theorems.funext) rot base : Id.map (λ f, happly f base) μLoop
    ... = loop                                : happly (Theorems.happlyFunext _ _ rot) base

  noncomputable hott def unitRight (x : S¹) : μ x base = x :=
  begin
    induction x; reflexivity; change _ = _;
    transitivity; apply transportOverInvolution (μ · base);
    transitivity; apply Id.map (· ⬝ idp base ⬝ loop);
    transitivity; apply Id.mapInv; apply Id.map;
    apply μLeft; transitivity; apply Id.map (· ⬝ loop);
    apply Id.reflRight; apply Id.invComp
  end

  hott def μLeftApLem {x : S¹} (p : base = x) :
    Id.map (μ · base) p = transport (base = ·) (unitRight x)⁻¹ p :=
  begin induction p; reflexivity end

  hott def μLeftAp  (p : Ω¹(S¹)) : Id.map (μ · base) p = p := μLeftApLem p
  hott def μRightAp (p : Ω¹(S¹)) : Id.map (μ base)   p = p := Equiv.idmap p

  noncomputable hott def unitComm (x : S¹) : μ base x = μ x base := (unitRight x)⁻¹

  noncomputable hott def mulInv (x : S¹) : base = μ x (inv x) :=
  begin
    induction x; exact loop; change _ = _;
    transitivity; apply transportComp (base = ·) (AS μ inv) loop;
    transitivity; apply transportComposition;
    transitivity; apply Id.map; apply Equiv.mapOverAS;
    transitivity; apply Id.map; apply Id.map; apply Circle.recβrule₂;
    transitivity; apply Id.map (· ⬝ Equiv.bimap μ loop loop⁻¹);
    symmetry; apply μRight; symmetry; transitivity;
    symmetry; apply μLeft; apply bimapComp
  end

  -- https://github.com/mortberg/cubicaltt/blob/master/examples/helix.ctt#L207
  hott def lemSetTorus {π : S¹ → S¹ → Type u} (setπ : hset (π base base))
    (f : Π y, π base y) (g : Π x, π x base) (p : f base = g base) : Π x y, π x y :=
  begin
    intro x; induction x; exact f; change _ = _; transitivity;
    apply transportOverPi; apply Theorems.funext; intro y; induction y;
    transitivity; apply Id.map; exact p; transitivity; apply apd; exact p⁻¹; apply setπ
  end

  noncomputable hott def isGroupoid : groupoid S¹ :=
  begin
    intros a b; change hset (a = b);
    fapply @indΩ (λ a, Π b, hset (a = b)) _ _ a <;> clear a;
    { intro b; fapply @indΩ (λ b, hset (base = b)) _ _ b <;> clear b;
      apply loopHset; intro; apply Structures.setIsProp };
    intro; apply piProp; intro; apply Structures.setIsProp
  end

  noncomputable hott def mulComm (x y : S¹) : μ x y = μ y x :=
  begin
    fapply @lemSetTorus (λ x y, μ x y = μ y x); apply loopHset;
    { intro z; symmetry; apply unitRight };
    { intro z; apply unitRight }; reflexivity
  end

  noncomputable hott def mulAssoc : Π x y z, μ x (μ y z) = μ (μ x y) z :=
  begin
    intro x; fapply @lemSetTorus (λ y z, μ x (μ y z) = μ (μ x y) z); apply isGroupoid;
    { intro z; apply Id.map (μ · z); exact (unitRight x)⁻¹ };
    { intro z; transitivity; apply Id.map; apply unitRight; symmetry; apply unitRight };
    { induction x; reflexivity; apply isGroupoid }
  end

  noncomputable hott def mulTrans (p q : Ω¹(S¹)) : bimap μ p q = p ⬝ q :=
  begin
    transitivity; apply bimapCharacterization;
    apply bimap; apply μLeftAp; apply μRightAp
  end

  noncomputable hott def mulTrans' (p q : Ω¹(S¹)) : bimap μ p q = q ⬝ p :=
  begin
    transitivity; apply bimapCharacterization';
    apply bimap; apply μRightAp; apply μLeftAp
  end

  noncomputable hott def comm (x y : Ω¹(S¹)) : x ⬝ y = y ⬝ x :=
  (mulTrans x y)⁻¹ ⬝ (mulTrans' x y)

  noncomputable hott def comm' (x y : Ω¹(S¹)) : x ⬝ y = y ⬝ x :=
    Equiv.bimap Id.trans (powerOfWinding x)⁻¹ (powerOfWinding y)⁻¹
  ⬝ Loop.powerComm Circle.loop (winding x) (winding y)
  ⬝ Equiv.bimap Id.trans (powerOfWinding y) (powerOfWinding x)

  noncomputable hott def Ωind₁ {π : (Ω¹(S¹)) → Type u}
    (zeroπ : π (idp base)) (succπ : Π x, π x → π (x ⬝ loop))
    (predπ : Π x, π x → π (x ⬝ loop⁻¹)) : Π x, π x :=
  begin
    intro x; apply transport π; apply powerOfWinding;
    fapply @Types.Integer.indsp (π ∘ power) _ _ _ (winding x);
    { exact zeroπ };
    { intros x ih; apply transport π;
      apply Loop.powerComp Circle.loop;
      apply succπ; exact ih };
    { intros x ih; apply transport π;
      apply Loop.powerCompPred;
      apply predπ; exact ih }
  end

  noncomputable hott def Ωind₂ {π : (Ω¹(S¹)) → Type u}
    (zeroπ : π Id.refl) (succπ : Π x, π x → π (loop ⬝ x))
    (predπ : Π x, π x → π (loop⁻¹ ⬝ x)) : Π x, π x :=
  begin
    fapply Ωind₁; exact zeroπ;
    { intros x ih; apply transport π; apply comm; apply succπ; exact ih };
    { intros x ih; apply transport π; apply comm; apply predπ; exact ih }
  end

  noncomputable hott def transComm {z : S¹} : Π (p q : z = z), p ⬝ q = q ⬝ p :=
  begin
    induction z; apply comm;
    apply Theorems.funext; intro;
    apply Theorems.funext; intro;
    apply isGroupoid
  end

  noncomputable hott def transportOverCircle {z : S¹} {f g : S¹ → S¹} {p : f = g}
    (μ : f z = f z) (η : f z = g z) : @transport (S¹ → S¹) (λ φ, φ z = φ z) f g p μ = η⁻¹ ⬝ μ ⬝ η :=
  begin induction p; symmetry; apply idConjIfComm; apply transComm end

  def halfway.φ : I → S¹ :=
  λ i, Interval.elim loop (i ∧ Interval.neg i)

  def halfway : base = base :=
  Interval.lam halfway.φ

  hott def halfway.const : halfway.φ ~ λ _, base :=
  begin
    intro x; induction x; reflexivity; reflexivity; change _ = _;
    transitivity; apply transportOverContrMap;
    transitivity; apply Id.reflRight;
    transitivity; apply Id.mapInv;
    transitivity; apply Id.map; apply mapOverComp;
    transitivity; apply Id.map; apply Id.map (map (elim loop));
    change _ = idp 0; apply Structures.propIsSet;
    apply Interval.intervalProp; reflexivity
  end

  hott def halfway.trivial : halfway = idp base :=
  begin
    transitivity; apply Equiv.mapWithHomotopy; apply halfway.const;
    transitivity; apply Id.reflRight; apply constmap
  end

  def natPow (x : S¹) : ℕ → S¹
  | Nat.zero   => base
  | Nat.succ n => μ x (natPow x n)

  def pow (x : S¹) : ℤ → S¹
  | Integer.pos n => natPow x n
  | Integer.neg n => natPow (inv x) (n + 1)

  def uarec {A : Type u} (φ : A ≃ A) : S¹ → Type u := rec A (ua φ)

  hott def Ωrec {A : Type u} (zero : A) (succ pred : A → A)
    (p : succ ∘ pred ~ id) (q : pred ∘ succ ~ id) : (Ω¹(S¹)) → A :=
  λ r, @transport S¹ (uarec ⟨succ, (⟨pred, q⟩, ⟨pred, p⟩)⟩) base base r zero

  section
    variable {A : Type u} (zero : A) (succ pred : A → A)
             (p : succ ∘ pred ~ id) (q : pred ∘ succ ~ id)

    hott def Ωrecβ₁ : Ωrec zero succ pred p q (idp base) = zero :=
    by reflexivity

    noncomputable hott def Ωrecβ₂ (r : Ω¹(S¹)) :
        Ωrec zero succ pred p q (r ⬝ loop)
      = succ (Ωrec zero succ pred p q r) :=
    begin
      transitivity; apply transportToTransportconst;
      transitivity; apply Id.map (transportconst · zero);
      transitivity; apply mapFunctoriality; apply Id.map; apply recβrule₂;
      transitivity; apply transportconstOverComposition;
      transitivity; apply ua.transportRule; apply Id.map succ;
      symmetry; apply transportToTransportconst
    end

    noncomputable hott def Ωrecβ₃ (r : Ω¹(S¹)) :
        Ωrec zero succ pred p q (r ⬝ loop⁻¹)
      = pred (Ωrec zero succ pred p q r) :=
    begin
      transitivity; apply transportToTransportconst;
      transitivity; apply Id.map (transportconst · zero);
      transitivity; apply mapFunctoriality; apply Id.map;
      transitivity; apply Id.mapInv; apply Id.map Id.symm; apply recβrule₂;
      transitivity; apply transportconstOverComposition;
      transitivity; apply transportconstOverInv;
      transitivity; apply ua.transportInvRule; apply Id.map pred;
      symmetry; apply transportToTransportconst
    end
  end

  hott def mult (p q : Ω¹(S¹)) : Ω¹(S¹) :=
  Id.map (rec base p) q

  hott def multZero (p : Ω¹(S¹)) : mult p (idp base) = idp base :=
  idp (idp base)

  hott def multSucc (p q : Ω¹(S¹)) : mult p (succ q) = mult p q ⬝ p :=
  begin transitivity; apply mapFunctoriality; apply Id.map; apply recβrule₂ end

  hott def multDistrRight (p q r : Ω¹(S¹)) : mult p (q ⬝ r) = mult p q ⬝ mult p r :=
  by apply mapFunctoriality

  hott def recComp (p q : Ω¹(S¹)) : rec base p ∘ rec base q ~ rec base (mult p q) :=
  begin
    fapply ind; reflexivity; change _ = _; transitivity;
    apply Equiv.transportOverHmtpy; transitivity;
    apply Id.map (· ⬝ _ ⬝ _); transitivity; apply mapInv;
    apply Id.map; transitivity; apply mapOverComp; apply Id.map (mult p); apply recβrule₂;
    transitivity; apply bimap; apply Id.reflRight; apply recβrule₂; apply Id.invComp
  end

  hott def multAssoc (p q r : Ω¹(S¹)) : mult (mult p q) r = mult p (mult q r) :=
  begin
    symmetry; transitivity; symmetry; apply mapOverComp (rec base q) (rec base p) r;
    transitivity; apply Equiv.mapWithHomotopy; apply recComp; apply Id.reflRight
  end

  hott def mulNegRight (p q : Ω¹(S¹)) : mult p q⁻¹ = (mult p q)⁻¹ :=
  by apply Id.mapInv

  hott def mapExt {B : Type u} (φ : S¹ → B) : φ ~ rec (φ base) (Id.map φ loop) :=
  begin
    fapply ind; reflexivity; change _ = _; transitivity; apply Equiv.transportOverHmtpy;
    transitivity; apply bimap; transitivity; apply Id.reflRight; apply Id.mapInv;
    apply recβrule₂; apply Id.invComp
  end

  section
    variable {B : Type u} (b : B) (p q : b = b) (H : p ⬝ q = q ⬝ p)

    hott def birec : S¹ → S¹ → B :=
    @rec (S¹ → B) (rec b p) (Theorems.funext (Circle.ind q (begin
      change _ = _; transitivity; apply Equiv.transportOverHmtpy;
      transitivity; apply bimap (· ⬝ q ⬝ ·);
      apply recβrule₃; apply recβrule₂;
      apply Id.idConjIfComm; exact H⁻¹
    end)))

    hott def birecβrule₁ : Id.map (birec b p q H base) loop = p :=
    by apply recβrule₂

    hott def birecβrule₂ : Id.map (birec b p q H · base) loop = q :=
    begin
      transitivity; apply Interval.mapHapply;
      transitivity; apply Id.map (happly · base); apply recβrule₂;
      apply happly (Theorems.happlyFunext _ _ _) base
    end

    hott def birecBimap : bimap (birec b p q H) loop loop = p ⬝ q :=
    begin
      transitivity; apply Equiv.bimapCharacterization';
      apply bimap; apply birecβrule₁; apply birecβrule₂
    end
  end

  open GroundZero.Types.Coproduct

  noncomputable hott def succNeqIdp : ua (Integer.succEquiv) ≠ idp ℤ :=
  begin
    intro H; apply @ua.succNeqZero 0; apply @inl.encode ℕ ℕ _ (inl 0);
    transitivity; symmetry; apply ua.transportRule Integer.succEquiv 0;
    apply ap (transportconst · 0) H
  end

  noncomputable hott def helixNontriv : helix ≠ (_ ↦ ℤ) :=
  begin
    intro H; apply succNeqIdp; transitivity; symmetry; apply recβrule₂;
    apply transport (λ φ, ap φ loop = idp (φ base)) H⁻¹; apply constmap
  end

  noncomputable hott def loopSpaceNontriv : ¬(Π (x y : S¹), (x = y) ≃ ℤ) :=
  begin
    intro H; apply helixNontriv; apply Theorems.funext; intro y;
    apply ua; transitivity; symmetry; apply family; apply H
  end
end Circle

def Torus := S¹ × S¹
notation "T²" => Torus

namespace Torus
  open Types.Product
  def b : T² := ⟨Circle.base, Circle.base⟩

  def inj₁ : S¹ → T² := Prod.mk Circle.base
  def inj₂ : S¹ → T² := (Prod.mk · Circle.base)

  -- poloidal and toroidal directions
  def p : b = b := prod (idp Circle.base) Circle.loop
  def q : b = b := prod Circle.loop (idp Circle.base)

  hott def Φ {π : Type u} {x x' y y' : π}
    (α : x = x') (β : y = y') :
    prod (idp x) β ⬝ prod α (idp y') =
    prod α (idp y) ⬝ prod (idp x') β :=
  begin induction α; induction β; reflexivity end

  hott def t : p ⬝ q = q ⬝ p :=
  Φ Circle.loop Circle.loop
end Torus

namespace Sphere
end Sphere

namespace Glome
end Glome

end HITs

namespace Types.Integer
  noncomputable def succPath := GroundZero.ua Integer.succEquiv

  noncomputable def shift : ℤ → ℤ = ℤ :=
  HITs.Loop.power succPath

  noncomputable hott def shiftComp (z : ℤ) :
    shift z ⬝ succPath = shift (Integer.succ z) :=
  HITs.Loop.powerComp succPath z
end Types.Integer

end GroundZero