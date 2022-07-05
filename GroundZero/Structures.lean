import GroundZero.Types.Unit
import GroundZero.Types.Sigma
import GroundZero.Types.Product
import GroundZero.Types.Coproduct

open GroundZero.Types.Unit
open GroundZero.Types.Id (map)
open GroundZero.Types (Coproduct idp fib)
open GroundZero.Types.Equiv (biinv)

namespace GroundZero
universe u v w k r

namespace Structures

hott def isLoop {A : Type u} {a : A} (p : a = a) := ¬(p = idp a)

hott def prop (A : Type u) := Π (a b : A), a = b

hott def propset := Σ (A : Type u), prop A
notation "Ω" => propset

hott def hset (A : Type u) := Π (a b : A) (p q : a = b), p = q
hott def Ens := Σ A, hset A

hott def groupoid (A : Type u) :=
Π (a b : A) (p q : a = b) (A B : p = q), A = B

hott def dec (A : Type u) := A + ¬A

hott def contr (A : Type u) := Σ (a : A), Π b, a = b

instance contr.dotted {A : Type u} (H : contr A) : Types.Id.dotted A := ⟨H.1⟩

inductive hlevel
| minusTwo
| succ : hlevel → hlevel

notation "ℕ₋₂" => hlevel
notation "−2" => hlevel.minusTwo
notation "−1" => hlevel.succ hlevel.minusTwo

namespace hlevel
  inductive le : hlevel → hlevel → Type
  | refl (a : hlevel)   : le a a
  | step (a b : hlevel) : le a b → le a (succ b)

  infix:50 " ≤ " => le

  hott def le.minusTwo : Π (n : hlevel), −2 ≤ n
  | −2     => le.refl −2
  | succ n => le.step _ _ (minusTwo n)

  noncomputable hott def le.succ (a b : hlevel) (ρ : a ≤ b) : succ a ≤ succ b :=
  begin induction ρ; apply le.refl; apply le.step; assumption end

  hott def add : hlevel → hlevel → hlevel
  | −2,            −2 => −2
  | −1,            −2 => −2
  | succ (succ n), −2 => n
  | n, succ (succ −2) => n
  | n, succ m         => succ (add n m)

  instance : HAdd hlevel hlevel hlevel := ⟨hlevel.add⟩

  hott def ofNat : ℕ → ℕ₋₂
  | Nat.zero   => succ (succ −2)
  | Nat.succ n => hlevel.succ (ofNat n)

  instance (n : ℕ) : OfNat ℕ₋₂ n := ⟨ofNat n⟩
end hlevel

def isNType : hlevel → Type u → Type u
| −2            => contr
| hlevel.succ n => λ A, Π (x y : A), isNType n (x = y)

notation "is-" n "-type" => isNType n

def nType (n : hlevel) : Type (u + 1) :=
Σ (A : Type u), is-n-type A

notation n "-Type" => nType n

hott def hlevel.cumulative {A : Type u} : Π (n : hlevel), is-n-type A → is-(hlevel.succ n)-type A
| −2,            H => λ x y, ⟨(H.2 x)⁻¹ ⬝ H.2 y, λ p, begin induction p; apply Types.Id.invComp end⟩
| hlevel.succ n, H => λ x y, cumulative n (H x y)

noncomputable hott def hlevel.strongCumulative (n m : hlevel) (ρ : n ≤ m) :
  Π {A : Type u}, (is-n-type A) → (is-m-type A) :=
begin
  induction ρ; intros; assumption;
  case step m ρ ih => {
    intros A G; apply @hlevel.cumulative;
    apply ih; assumption
  }
end

hott def contrImplProp {A : Type u} (h : contr A) : prop A :=
λ a b, (h.2 a)⁻¹ ⬝ (h.2 b)

def emptyIsProp : prop 𝟎 :=
begin intros x; induction x end

def unitIsProp : prop 𝟏 :=
begin intros x y; induction x; induction y; reflexivity end

hott def contrEquivUnit {A : Type u} (h : contr A) : A ≃ 𝟏 :=
begin
  existsi (λ _, ★); apply Types.Qinv.toBiinv;
  existsi (λ _, h.1) <;> apply Prod.mk <;> intro x;
  induction x; reflexivity; apply h.2
end

hott def zeroMorphismContr {A : Type u} : contr (A → 𝟏) :=
⟨λ _, ★, λ f, HITs.Interval.funext (λ x, unitIsProp ★ (f x))⟩

hott def zeroMorphismEqv {A : Type u} : (A → 𝟏) ≃ 𝟏 :=
contrEquivUnit zeroMorphismContr

hott def familyOverUnit (C : 𝟏 → Type u) : (Π x, C x) ≃ (C ★) :=
begin
  fapply Sigma.mk; { intro φ; apply φ }; apply Types.Qinv.toBiinv;
  fapply Sigma.mk; { intros c x; induction x; exact c };
  fapply Prod.mk; { intro x; reflexivity };
  { intro ψ; apply HITs.Interval.funext; intro x; induction x; reflexivity }
end

hott def cozeroMorphismEqv {A : Type u} : (𝟏 → A) ≃ A :=
familyOverUnit (λ _, A)

hott def terminalArrow {A : Type u} : A ≃ (𝟏 → A) :=
⟨λ x _, x, Types.Qinv.toBiinv _ ⟨λ φ, φ ★, (λ φ, HITs.Interval.funext (λ ★, idp _), idp)⟩⟩

hott def contrTypeEquiv {A : Type u} {B : Type v}
  (p : contr A) (q : contr B) : A ≃ B := calc
      A ≃ 𝟏 : contrEquivUnit.{_, 0} p
    ... ≃ B : Types.Equiv.symm (contrEquivUnit q)

hott def prodUnitEquiv (A : Type u) : 𝟏 × A ≃ A :=
begin existsi Prod.snd; apply Prod.mk <;> existsi Prod.mk ★ <;> { intro; reflexivity } end

hott def unitProdEquiv : A × 𝟏 ≃ A :=
begin existsi Prod.fst; apply Prod.mk <;> existsi (Prod.mk · ★) <;> { intro x; reflexivity } end

def boolToUniverse : 𝟐 → Type
| true  => 𝟏
| false => 𝟎

hott def ffNeqTt : false ≠ true :=
λ p, Types.Equiv.transport boolToUniverse p⁻¹ ★

hott def functionSpace : ¬(Π (A B : Type), prop (A → B)) :=
λ H, ffNeqTt (Types.Equiv.Homotopy.Id (H 𝟐 𝟐 id not) false)

hott def autoContr {A : Type u} (x : A) (H : prop (A → A)) : prop A :=
begin
  apply contrImplProp; existsi x;
  apply Types.Equiv.Homotopy.Id; apply H
end

section
  open Types.Equiv Types.Id

  hott def propIsSet {A : Type u} (r : prop A) : hset A :=
  begin
    intros x y p q; have g := r x; apply Types.Id.trans;
    symmetry; apply rewriteComp;
    exact (apd g p)⁻¹ ⬝ transportComposition p (g x);
    induction q; apply invComp
  end

  hott def setImplGroupoid {A : Type u} (r : hset A) : groupoid A :=
  begin
    intros a b p q η μ; have g := r _ _ p; apply Types.Id.trans;
    symmetry; apply rewriteComp; transitivity; symmetry; exact apd g η;
    apply transportComposition; induction μ; apply invComp
  end

  hott def emptyIsSet : hset 𝟎 := propIsSet emptyIsProp
  hott def unitIsSet  : hset 𝟏 := propIsSet unitIsProp

  hott def contrIsProp {A : Type u} : prop (contr A) :=
  begin
    intro ⟨x, u⟩ ⟨y, v⟩; have p := u y;
    induction p; apply map;
    apply HITs.Interval.funext; intro a;
    apply propIsSet (contrImplProp ⟨x, u⟩)
  end

  -- TODO: apply “repeat” tactic
  hott def propIsProp {A : Type u} : prop (prop A) :=
  begin
    intros f g;
    apply HITs.Interval.funext; intro;
    apply HITs.Interval.funext; intro;
    apply propIsSet; assumption
  end

  hott def setIsProp {A : Type u} : prop (hset A) :=
  begin
    intros f g;
    apply HITs.Interval.funext; intro;
    apply HITs.Interval.funext; intro;
    apply HITs.Interval.funext; intro;
    apply HITs.Interval.funext; intro;
    apply setImplGroupoid; assumption
  end

  hott def ntypeIsProp : Π (n : hlevel) {A : Type u}, prop (is-n-type A)
  | −2            => contrIsProp
  | hlevel.succ n => λ p q, HITs.Interval.funext (λ x, HITs.Interval.funext (λ y, ntypeIsProp n _ _))

  hott def functionToContr {A : Type u} : prop (A → contr A) :=
  begin intros f g; apply HITs.Interval.funext; intro x; apply contrIsProp end
end

hott def retract (B : Type u) (A : Type v) :=
Σ (r : A → B) (s : B → A), r ∘ s ~ id

hott def retract.section {B : Type u} {A : Type v} (w : retract B A) : B → A := w.2.1

hott def contrRetract {A : Type u} {B : Type v} : retract B A → contr A → contr B :=
λ ⟨r, s, ε⟩ ⟨a₀, p⟩, ⟨r a₀, λ b, map r (p (s b)) ⬝ (ε b)⟩

hott def retract.path {A : Type u} {B : Type v} :
  Π (H : retract B A) {a b : B},
  retract (a = b) (H.section a = H.section b) :=
λ ⟨r, s, ε⟩ a b, ⟨λ q, (ε a)⁻¹ ⬝ (@map A B _ _ r q) ⬝ (ε b), map s,
begin
  intro p; transitivity; symmetry; apply Types.Id.assoc;
  symmetry; apply Types.Equiv.invRewriteComp;
  transitivity; apply map (· ⬝ p); apply Types.Id.invInv;
  transitivity; apply map (ε a ⬝ ·); symmetry; apply Types.Equiv.idmap;
  transitivity; apply Types.Equiv.homotopySquare ε p;
  apply map (· ⬝ ε b); apply Types.Equiv.mapOverComp
end⟩

hott def equivRespectsRetraction : Π {n : ℕ₋₂} {A : Type u} {B : Type v},
  retract B A → is-n-type A → is-n-type B
| −2            => contrRetract
| hlevel.succ n => λ G H a b, equivRespectsRetraction (retract.path G) (H _ _)

hott def equivInducesRetraction {A : Type u} {B : Type v} : A ≃ B → retract B A :=
λ ⟨f, (_, ⟨g, ε⟩)⟩, ⟨f, g, ε⟩

hott def ntypeRespectsEquiv (n : ℕ₋₂) {A : Type u} {B : Type v} :
  A ≃ B → is-n-type A → is-n-type B :=
equivRespectsRetraction ∘ equivInducesRetraction

hott def ntypeRespectsSigma : Π (n : ℕ₋₂) {A : Type u} {B : A → Type v},
  is-n-type A → (Π x, is-n-type (B x)) → is-n-type (Σ x, B x)
| −2            => λ ⟨a₀, p⟩ B, ⟨⟨a₀, (B a₀).1⟩, λ ⟨a, b⟩, Types.Sigma.prod (p a) (contrImplProp (B a) _ _)⟩
| hlevel.succ n => λ A B p q, ntypeRespectsEquiv n (Types.Equiv.symm Types.Sigma.sigmaPath)
                                (ntypeRespectsSigma n (A p.1 q.1) (λ x, B q.1 _ _))

inductive propSquash (A : Type u) : Prop
| elem : A → propSquash A

inductive Lift (A : Prop) : Type
| elem : A → Lift A

def Squash := Lift ∘ propSquash

def Squash.elem {A : Type u} : A → Squash A :=
Lift.elem ∘ propSquash.elem

def Squash.uniq {A : Type u} : Π (a b : Squash A), a = b :=
λ (Lift.elem _) (Lift.elem _), idp _

def Squash.prop {A : Type u} {B : Prop} (f : A → B) : Squash A → B :=
λ (Lift.elem (propSquash.elem x)), f x

def Squash.Lift {A : Type u} {B : Type v}
  (f : A → B) : Squash A → Squash B :=
Lift.elem ∘ Squash.prop (propSquash.elem ∘ f)

def K (A : Type u) := Π (a : A) (p : a = a), p = idp a

hott def KIffSet (A : Type u) : K A ↔ hset A :=
begin
  fapply Prod.mk;
  { intros H x y p q; induction q; apply H };
  { intros H a p; apply H }
end

hott def lemProp {A : Type u} (h : A → prop A) : prop A :=
λ a, h a a

hott def lemContr {A : Type u} (h : A → contr A) : prop A :=
λ a, contrImplProp (h a) a

def isContrFiber {A : Type u} {B : Type v} (f : A → B) :=
Π (y : B), contr (fib f y)

hott def propEquivLemma {A : Type u} {B : Type v}
  (F : prop A) (G : prop B) (f : A → B) (g : B → A) : A ≃ B :=
⟨f, (⟨g, λ _, F _ _⟩, ⟨g, λ _, G _ _⟩)⟩

hott def minusTwoEqvContr {A : Type u} : (is-(−2)-type A) ≃ contr A :=
by reflexivity

hott def minusOneEqvProp {A : Type u} : (is-(−1)-type A) ≃ prop A :=
begin
  apply propEquivLemma; apply ntypeIsProp; apply propIsProp;
  { intros H a b; exact (H a b).1 };
  { intros H a b; existsi H a b; apply propIsSet H }
end

hott def equivFunext {A : Type u} {η μ : A → Type v}
  (H : Π x, η x ≃ μ x) : (Π x, η x) ≃ (Π x, μ x) :=
begin
  existsi (λ (f : Π x, η x) (x : A), (H x).forward (f x)); apply Prod.mk;
  { existsi (λ (f : Π x, μ x) (x : A), (H x).left (f x));
    intro f; apply HITs.Interval.funext;
    intro x; apply (H x).leftForward };
  { existsi (λ (f : Π x, μ x) (x : A), (H x).right (f x));
    intro f; apply HITs.Interval.funext;
    intro x; apply (H x).forwardRight }
end

hott def zeroEqvSet {A : Type u} : (is-0-type A) ≃ hset A := calc
  (is-0-type A) ≃ (Π (x y : A), is-(−1)-type (x = y)) : by reflexivity
            ... ≃ (Π (x y : A), prop (x = y)) :
                  begin apply equivFunext; intro x;
                        apply equivFunext; intro y;
                        apply minusOneEqvProp end
            ... ≃ hset A : by reflexivity

hott def oneEqvGroupoid {A : Type u} : (is-1-type A) ≃ groupoid A := calc
  (is-1-type A) ≃ (Π (x y : A), is-0-type (x = y)) : by reflexivity
            ... ≃ (Π (x y : A), hset (x = y)) :
                   begin apply equivFunext; intro x;
                         apply equivFunext; intro y;
                         apply zeroEqvSet end
            ... ≃ groupoid A : by reflexivity

hott def propIsNType {A : Type u} (H : prop A) : Π n, is-(hlevel.succ n)-type A
| −2            => minusOneEqvProp.left H
| hlevel.succ n => hlevel.cumulative (hlevel.succ n) (propIsNType H n)

hott def hsetRespectsEquiv {A : Type u} {B : Type v} :
  A ≃ B → hset A → hset B :=
begin
  intros e H; apply zeroEqvSet.forward;
  apply ntypeRespectsEquiv 0 e;
  apply zeroEqvSet.left;
  assumption
end

hott def hsetRespectsSigma {A : Type u} {B : A → Type v}
  (H : hset A) (G : Π x, hset (B x)) : hset (Σ x, B x) :=
begin
  apply zeroEqvSet.forward; apply ntypeRespectsSigma 0;
  { apply zeroEqvSet.left; intros x y; apply H };
  { intro x; apply zeroEqvSet.left; apply G }
end

hott def propRespectsEquiv {A : Type u} {B : Type v} :
  A ≃ B → prop A → prop B :=
begin
  intros e H; apply minusOneEqvProp.forward;
  apply ntypeRespectsEquiv −1 e;
  apply minusOneEqvProp.left;
  assumption
end

hott def contrRespectsEquiv {A : Type u} {B : Type v} :
  A ≃ B → contr A → contr B :=
ntypeRespectsEquiv −2

hott def productProp {A : Type u} {B : Type v}
  (h : prop A) (g : prop B) : prop (A × B) :=
begin
  intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩;
  have p := h x₁ x₂; have q := g y₁ y₂;
  induction p; induction q; reflexivity
end

hott def prodHset {A : Type u} {B : Type v}
  (p : hset A) (q : hset B) : hset (A × B) :=
begin
  apply hsetRespectsEquiv;
  apply Types.Sigma.const;
  apply hsetRespectsSigma;
  apply p; intro x; apply q
end

hott def piProp {A : Type u} {B : A → Type v}
  (H : Π x, prop (B x)) : prop (Π x, B x) :=
λ f g, HITs.Interval.funext (λ x, H x (f x) (g x))

hott def sigProp {A : Type u} {B : A → Type v}
  (H : prop A) (G : Π x, prop (B x)) : prop (Σ x, B x) :=
begin intros w₁ w₂; fapply Types.Sigma.prod; apply H; apply G end

hott def implProp {A : Type u} {B : Type v} (H : prop B) : prop (A → B) :=
piProp (λ _, H)

hott def notIsProp {A : Type u} : prop (¬ A) :=
implProp emptyIsProp

hott def reflMereRel {A : Type u} (R : A → A → Type v) (h : Π x y, prop (R x y))
  (ρ : Π x, R x x) (f : Π x y, R x y → x = y) : hset A :=
begin
  apply (KIffSet _).left; intros a p;
  apply Types.Id.transCancelLeft (f a a (ρ a));
  transitivity; symmetry; apply Types.Equiv.transportComposition;
  transitivity; apply Types.Equiv.liftedHapply (R a); apply Types.Equiv.apd (f a) p;
  transitivity; apply map (f a a) (h _ _ _ (ρ a)); symmetry; apply Types.Id.reflRight
end

hott def doubleNegEq {A : Type u} (h : Π (x y : A), ¬¬(x = y) → x = y) : hset A :=
begin
  fapply reflMereRel;
  { intros x y; exact ¬¬(x = y) };
  { intros x y; apply implProp; apply emptyIsProp };
  { intro x; intros f; apply f; reflexivity };
  { exact h }
end

hott def lemToDoubleNeg {A : Type u} : dec A → (¬¬A → A)
| Sum.inl x => λ _, x
| Sum.inr t => λ g, Proto.Empty.elim (g t)

hott def Hedberg {A : Type u} : (Π (x y : A), dec (x = y)) → hset A :=
begin intro H; apply doubleNegEq; intros x y; apply lemToDoubleNeg; apply H x y end

hott def boolEqTotal (x : 𝟐) : (x = false) + (x = true) :=
begin induction x using Bool.casesOn; left; reflexivity; right; reflexivity end

hott def boolDecEq (x y : 𝟐) : dec (x = y) :=
begin
  induction x using Bool.casesOn <;>
  induction y using Bool.casesOn;
  { left; reflexivity };
  { right; apply ffNeqTt };
  { right; intro p; apply ffNeqTt; exact p⁻¹ };
  { left; reflexivity }
end

hott def boolIsSet : hset 𝟐 := Hedberg boolDecEq

section
  open GroundZero.Types
  hott def zeroPath {A B : 0-Type} (p : A.fst = B.fst) : A = B :=
  begin fapply Sigma.prod; exact p; apply ntypeIsProp end

  hott def zeroPathRefl (A : 0-Type) : @zeroPath A A Id.refl = Id.refl :=
  begin
    transitivity; apply Id.map (Sigma.prod (idp _)); change _ = Id.refl;
    apply propIsSet (ntypeIsProp 0); apply Sigma.prodRefl
  end
end

hott def Identity.ens {A : Type u} (H : hset A) : hset (Proto.Identity A) :=
begin apply hsetRespectsEquiv; apply Types.Equiv.identityEqv; assumption end

hott def zeroEquiv (A B : 0-Type) := A.1 ≃ B.1
infix:25 " ≃₀ " => zeroEquiv

end Structures

-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/tiny-library.html
-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/hsetfunext.html
def singl {A : Type u} (a : A) :=
Σ b, a = b

namespace singl
  def trivialLoop {A : Type u} (a : A) : singl a :=
  ⟨a, by reflexivity⟩

  hott def pathFromTrivialLoop {A : Type u} {a b : A}
    (r : a = b) : trivialLoop a = ⟨b, r⟩ :=
  begin induction r; reflexivity end

  hott def contr {A : Type u} (a : A) : Structures.contr (singl a) :=
  ⟨trivialLoop a, λ t, pathFromTrivialLoop t.2⟩

  hott def prop {A : Type u} (a : A) : Structures.prop (singl a) :=
  Structures.contrImplProp (contr a)
end singl

namespace Theorems
  open GroundZero.Structures GroundZero.Types.Equiv GroundZero.Types

  hott def naive {A : Type u} {B : A → Type v} {f g : Π x, B x} : f ~ g → f = g :=
  HITs.Interval.funext

  hott def weak {A : Type u} {B : A → Type v} (H : Π x, contr (B x)) : contr (Π x, B x) :=
  begin existsi (λ x, (H x).1); intro f; apply naive; intro x; apply (H x).2 end

  section
    variable {A : Type u} {B : A → Type v}

    hott def isContrSigmaHomotopy (f : Π x, B x) : contr (Σ g, f ~ g) :=
    let r (k : Π x, Σ y, f x = y) :=
    @Sigma.mk _ (λ g, f ~ g) (λ x, (k x).1) (λ x, (k x).2);
    let s (g : Π x, B x) (h : f ~ g) x :=
    Sigma.mk (g x) (h x);
    begin
      existsi Sigma.mk f (Homotopy.id f); intro ⟨g, H⟩;
      change r (λ x, Sigma.mk (f x) (idp _)) = r (s g H);
      apply Id.map r; apply contrImplProp;
      apply weak; intro x; apply singl.contr
    end

    variable (f : Π x, B x) {π : Π g (h : f ~ g), Type w} (r : π f (Homotopy.id f))
    hott def homotopyInd (g : Π x, B x) (h : f ~ g) : π g h :=
    @transport (Σ g, f ~ g) (λ (p : Σ g, f ~ g), π p.fst p.snd)
      ⟨f, Homotopy.id f⟩ ⟨g, h⟩
      (contrImplProp (isContrSigmaHomotopy f) _ _) r

    hott def homotopyIndId : homotopyInd f r f (Homotopy.id f) = r :=
    begin
      transitivity; apply Id.map
        (λ p, @transport (Σ g, f ~ g) (λ p, π p.fst p.snd)
           ⟨f, Homotopy.id f⟩ ⟨f, Homotopy.id f⟩ p r);
      change _ = idp _; apply propIsSet; apply contrImplProp;
      apply isContrSigmaHomotopy; reflexivity
    end
  end

  hott def funext {A : Type u} {B : A → Type v}
    {f g : Π x, B x} : (f ~ g) → (f = g) :=
  @homotopyInd _ _ f (λ g x, f = g) (idp _) g

  hott def funextHapply {A : Type u} {B : A → Type v}
    {f g : Π x, B x} : funext ∘ @HITs.Interval.happly A B f g ~ id :=
  begin
    intro p; induction p; change funext (Homotopy.id _) = idp _;
    dsimp [funext]; apply homotopyIndId f
  end

  hott def happlyFunext {A : Type u} {B : A → Type v}
    (f g : Π x, B x) : HITs.Interval.happly ∘ @funext A B f g ~ id :=
  begin
    intro H; fapply @homotopyInd _ _ f (λ g G, HITs.Interval.happly (funext G) = G) _ g H;
    change _ = HITs.Interval.happly (idp _); apply Id.map HITs.Interval.happly;
    change homotopyInd _ _ _ _ = _; apply homotopyIndId
  end

  hott def full {A : Type u} {B : A → Type v} {f g : Π x, B x} : (f = g) ≃ (f ~ g) :=
  begin
    existsi HITs.Interval.happly; apply Qinv.toBiinv; existsi funext;
    apply Prod.mk; apply happlyFunext; apply funextHapply
  end

  hott def funextId {A : Type u} {B : A → Type v}
    {f : Π x, B x} : funext (Homotopy.id f) = idp f :=
  homotopyIndId _ _

  open GroundZero.Types.Equiv (transport)
  hott def mapHomotopy {A : Type u} {B : Type v} {a b : A} (f g : A → B) (p : a = b) (q : f ~ g) :
    Id.map g p = @transport (A → B) (λ h, h a = h b) f g (funext q) (Id.map f p) :=
  begin
    induction p; symmetry; transitivity; apply Types.Equiv.transportOverHmtpy;
    transitivity; apply Id.map (· ⬝ Id.map (λ (h : A → B), h a) (funext q));
    apply Id.reflRight; transitivity; symmetry; apply mapFunctoriality (λ (h : A → B), h a);
    transitivity; apply Id.map; apply Id.invComp; reflexivity
  end
end Theorems

namespace Structures
  hott def piRespectsNType :
    Π (n : ℕ₋₂) {A : Type u} {B : A → Type v},
      (Π x, is-n-type (B x)) → is-n-type (Π x, B x)
  | −2            => λ H, ⟨λ x, (H x).1, λ φ, Theorems.funext (λ x, (H x).2 (φ x))⟩
  | hlevel.succ n => λ H f g, ntypeRespectsEquiv n (Types.Equiv.symm Theorems.full)
                                (piRespectsNType n (λ x, H x _ _))

  hott def piHset {A : Type u} {B : A → Type v}
    (H : Π x, hset (B x)) : hset (Π x, B x) :=
  begin
    apply zeroEqvSet.forward; apply piRespectsNType 0;
    intro x; apply zeroEqvSet.left; apply H
  end
end Structures

hott def iter (A B : Type) : ℕ → Type
| Nat.zero   => B
| Nat.succ n => Coproduct (iter A B n) A

hott def pt := iter 𝟏

hott def vect (A : Type u) : ℕ → Type u
| Nat.zero   => 𝟏
| Nat.succ n => A × vect A n

hott def vect.const {A : Type u} (a : A) : Π n, vect A n
| Nat.zero   => ★
| Nat.succ n => (a, const a n)

hott def vect.map {A : Type u} {B : Type v} (f : A → B) :
  Π {n : ℕ}, vect A n → vect B n
| Nat.zero   => λ _, ★
| Nat.succ n => λ v, (f v.1, map f v.2)

section
  open GroundZero.Types.Equiv (transport subst)

  hott def vect.subst {A B : Type u} (p : A = B) (f : B → A) {n : ℕ} (v : vect A n) :
    vect.map f (@transport (Type u) (λ δ, vect δ n) A B p v) =
    vect.map (λ (x : A), f (transport id p x)) v :=
  begin induction p; reflexivity end
end

hott def vect.idfunc {A : Type u} : Π {n : ℕ} (f : A → A)
  (H : f ~ id) (v : vect A n), vect.map f v = v
| Nat.zero,   f, H, v => idp v
| Nat.succ n, f, H, v => Types.Product.prod (H v.1) (idfunc f H v.2)

hott def vect.id {A : Type u} {n : ℕ} (v : vect A n) : vect.map id v = v :=
begin apply vect.idfunc; reflexivity end

hott def vect.comp {A : Type u} {B : Type v} {γ : Type w} :
  Π {n : ℕ} (f : A → B) (g : B → γ) (v : vect A n), vect.map g (vect.map f v) = vect.map (g ∘ f) v
| Nat.zero,   f, g, v => idp _
| Nat.succ n, f, g, v => Types.Product.prod (idp _) (comp f g v.2)

hott def vect.constMap {A : Type u} {B : Type v} (a : A) (f : A → B) :
  Π {n : ℕ}, vect.map f (vect.const a n) = vect.const (f a) n
| Nat.zero   => idp _
| Nat.succ n => Types.Product.prod (idp _) (constMap a f)

hott def Finite := iter 𝟏 𝟎
@[matchPattern] def Finite.zero {n : ℕ} : Finite (n + 1) := Sum.inr ★
@[matchPattern] def Finite.succ {n : ℕ} : Finite n → Finite (n + 1) := Sum.inl

def LEMinf := Π (A : Type u), A + ¬A
notation "LEM∞" => LEMinf

open Structures (prop propset)
hott def hrel (A : Type u) := A → A → propset.{v}

section
  variable {A : Type u} (R : hrel A)

  def isrefl  := Π a, (R a a).1
  def issymm  := Π a b, (R a b).1 → (R b a).1
  def istrans := Π a b c, (R a b).1 → (R b c).1 → (R a c).1

  def iseqrel := isrefl R × issymm R × istrans R
end

hott def eqrel (A : Type u) := Σ φ, @iseqrel A φ

-- TODO: repeat
hott def iseqrel.prop {A : Type u} {R : hrel A} : prop (iseqrel R) :=
begin
  apply Structures.productProp;
  { intros f g; apply Theorems.funext;
    intro x; apply (R x x).2 };
  apply Structures.productProp;
  { intros f g;
    apply Theorems.funext; intro;
    apply Theorems.funext; intro;
    apply Theorems.funext; intro;
    apply (R _ _).2 };
  { intros f g;
     apply Theorems.funext; intro;
    apply Theorems.funext; intro;
    apply Theorems.funext; intro;
    apply Theorems.funext; intro;
    apply Theorems.funext; intro;
    apply (R _ _).2 }
end

section
  variable {A : Type u} (R : eqrel.{u, v} A)

  hott def eqrel.rel : hrel A := R.1
  hott def eqrel.iseqv : iseqrel R.rel := R.2

  hott def eqrel.apply (a b : A) : Type v :=
  (R.rel a b).1

  hott def eqrel.prop (a b : A) : prop (R.apply a b) :=
  (R.rel a b).2

  -- Accessors
  hott def eqrel.refl (a : A) : R.apply a a :=
  R.2.1 a

  hott def eqrel.symm {a b : A} : R.apply a b → R.apply b a :=
  R.2.2.1 a b

  hott def eqrel.trans {a b c : A} :
    R.apply a b → R.apply b c → R.apply a c :=
  R.2.2.2 a b c
end

hott def eqrel.eq {A : Type u} {x y : eqrel A} (p : x.rel = y.rel) : x = y :=
begin apply Types.Sigma.prod p; apply iseqrel.prop end

hott def iffOverPi {A : Type u} {B : A → Type v} {B' : A → Type w}
  (φ : Π x, B x ↔ B' x) : (Π x, B x) ↔ (Π x, B' x) :=
begin apply Prod.mk; { intros f x; apply (φ x).left; apply f }; { intros g x; apply (φ x).right; apply g } end

hott def hcommSquare (P : Type k) (A : Type u) (B : Type v) (C : Type w) :=
Σ (f : A → C) (g : B → C) (h : P → A) (k : P → B), f ∘ h = g ∘ k

hott def pullback {A : Type u} {B : Type v}
  (C : Type w) (f : A → C) (g : B → C) :=
Σ (p : A × B), f p.1 = g p.2

namespace hcommSquare
  variable {P : Type k} {A : Type u} {B : Type v} {C : Type w}

  def top   (η : hcommSquare P A B C) : P → A := η.2.2.1
  def bot   (η : hcommSquare P A B C) : B → C := η.2.1
  def left  (η : hcommSquare P A B C) : P → B := η.2.2.2.1
  def right (η : hcommSquare P A B C) : A → C := η.1

  def naturality (η : hcommSquare P A B C) : η.right ∘ η.top = η.bot ∘ η.left := η.2.2.2.2

  hott def induced (η : hcommSquare P A B C) (X : Type r) :
    (X → P) → @pullback (X → A) (X → B) (X → C) (λ f, right η ∘ f) (λ g, bot η ∘ g) :=
  λ φ, ⟨(top η ∘ φ, left η ∘ φ), @map (P → C) (X → C) (right η ∘ top η) (bot η ∘ left η) (· ∘ φ) η.naturality⟩

  hott def isPullback (η : hcommSquare P A B C) :=
  Π (X : Type (max u v w k)), biinv (induced η X)
end hcommSquare

hott def pullbackSquare (P : Type k) (A : Type u) (B : Type v) (C : Type w) :=
Σ (η : hcommSquare P A B C), η.isPullback

namespace Types.Equiv
  open GroundZero.Structures

  -- 1-1 correspondence
  def Corr (A : Type u) (B : Type v) :=
  Σ (R : A → B → Type w), (Π a, contr (Σ b, R a b)) × (Π b, contr (Σ a, R a b))

  open GroundZero.Types
  variable {A : Type u} {A' : Type v} {B : Type u'} {B' : Type v'}

  hott def prodBiinv {f : A → A'} {g : B → B'}
    (e₁ : biinv f) (e₂ : biinv g) : biinv (Product.bimap f g) :=
  (⟨Product.bimap e₁.1.1 e₂.1.1, λ w, Product.prod (e₁.1.2 w.1) (e₂.1.2 w.2)⟩,
   ⟨Product.bimap e₁.2.1 e₂.2.1, λ w, Product.prod (e₁.2.2 w.1) (e₂.2.2 w.2)⟩)

  hott def prodEquiv (e₁ : A ≃ A') (e₂ : B ≃ B') : (A × B) ≃ (A' × B') :=
  ⟨Product.bimap e₁.1 e₂.1, prodBiinv e₁.2 e₂.2⟩
end Types.Equiv

end GroundZero