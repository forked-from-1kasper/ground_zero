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

hott def isLoop {α : Type u} {a : α} (p : a = a) := ¬(p = idp a)

hott def prop (α : Type u) := Π (a b : α), a = b

hott def propset := Σ (α : Type u), prop α
notation "Ω" => propset

hott def hset (α : Type u) := Π (a b : α) (p q : a = b), p = q
hott def Ens := Σ α, hset α

hott def groupoid (α : Type u) :=
Π (a b : α) (p q : a = b) (α β : p = q), α = β

hott def dec (α : Type u) := α + ¬α

hott def contr (α : Type u) := Σ (a : α), Π b, a = b

instance contr.dotted {α : Type u} (H : contr α) : Types.Id.dotted α := ⟨H.1⟩

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
| hlevel.succ n => λ α, Π (x y : α), isNType n (x = y)

notation "is-" n "-type" => isNType n

def nType (n : hlevel) : Type (u + 1) :=
Σ (α : Type u), is-n-type α

notation n "-Type" => nType n

hott def hlevel.cumulative {α : Type u} : Π (n : hlevel), is-n-type α → is-(hlevel.succ n)-type α
| −2,            H => λ x y, ⟨(H.2 x)⁻¹ ⬝ H.2 y, λ p, begin induction p; apply Types.Id.invComp end⟩
| hlevel.succ n, H => λ x y, cumulative n (H x y)

noncomputable hott def hlevel.strongCumulative (n m : hlevel) (ρ : n ≤ m) :
  Π {α : Type u}, (is-n-type α) → (is-m-type α) :=
begin
  induction ρ; intros; assumption;
  case step m ρ ih => {
    intros α G; apply @hlevel.cumulative;
    apply ih; assumption
  }
end

hott def contrImplProp {α : Type u} (h : contr α) : prop α :=
λ a b, (h.2 a)⁻¹ ⬝ (h.2 b)

def emptyIsProp : prop 𝟎 :=
begin intros x; induction x end

def unitIsProp : prop 𝟏 :=
begin intros x y; induction x; induction y; reflexivity end

hott def contrEquivUnit {α : Type u} (h : contr α) : α ≃ 𝟏 :=
begin
  existsi (λ _, ★); apply Types.Qinv.toBiinv;
  existsi (λ _, h.1) <;> apply Prod.mk <;> intro x;
  induction x; reflexivity; apply h.2
end

hott def zeroMorphismContr {α : Type u} : contr (α → 𝟏) :=
⟨λ _, ★, λ f, HITs.Interval.funext (λ x, unitIsProp ★ (f x))⟩

hott def zeroMorphismEqv {α : Type u} : (α → 𝟏) ≃ 𝟏 :=
contrEquivUnit zeroMorphismContr

hott def familyOverUnit (C : 𝟏 → Type u) : (Π x, C x) ≃ (C ★) :=
begin
  fapply Sigma.mk; { intro φ; apply φ }; apply Types.Qinv.toBiinv;
  fapply Sigma.mk; { intros c x; induction x; exact c };
  fapply Prod.mk; { intro x; reflexivity };
  { intro ψ; apply HITs.Interval.funext; intro x; induction x; reflexivity }
end

hott def cozeroMorphismEqv {α : Type u} : (𝟏 → α) ≃ α :=
familyOverUnit (λ _, α)

hott def contrTypeEquiv {α : Type u} {β : Type v}
  (p : contr α) (q : contr β) : α ≃ β := calc
      α ≃ 𝟏 : contrEquivUnit p
    ... ≃ β : Types.Equiv.symm (contrEquivUnit q)

hott def prodUnitEquiv (α : Type u) : 𝟏 × α ≃ α :=
begin
  existsi Prod.snd; apply Prod.mk <;> existsi Prod.mk ★;
  { intro ⟨x, y⟩; induction x; reflexivity };
  { intro x; reflexivity }
end

def boolToUniverse : 𝟐 → Type
| true  => 𝟏
| false => 𝟎

hott def ffNeqTt : false ≠ true :=
λ p, Types.Equiv.transport boolToUniverse p⁻¹ ★

hott def functionSpace : ¬(Π (α β : Type), prop (α → β)) :=
λ H, ffNeqTt (Types.Equiv.Homotopy.Id (H 𝟐 𝟐 id not) false)

hott def autoContr {α : Type u} (x : α) (H : prop (α → α)) : prop α :=
begin
  apply contrImplProp; existsi x;
  apply Types.Equiv.Homotopy.Id; apply H
end

section
  open Types.Equiv Types.Id

  hott def propIsSet {α : Type u} (r : prop α) : hset α :=
  begin
    intros x y p q; have g := r x; apply Types.Id.trans;
    symmetry; apply rewriteComp;
    exact (apd g p)⁻¹ ⬝ transportComposition p (g x);
    induction q; apply invComp
  end

  hott def setImplGroupoid {α : Type u} (r : hset α) : groupoid α :=
  begin
    intros a b p q η μ; have g := r _ _ p; apply Types.Id.trans;
    symmetry; apply rewriteComp; transitivity; symmetry; exact apd g η;
    apply transportComposition; induction μ; apply invComp
  end

  hott def emptyIsSet : hset 𝟎 := propIsSet emptyIsProp
  hott def unitIsSet  : hset 𝟏 := propIsSet unitIsProp

  hott def contrIsProp {α : Type u} : prop (contr α) :=
  begin
    intro ⟨x, u⟩ ⟨y, v⟩; have p := u y;
    induction p; apply map;
    apply HITs.Interval.funext; intro a;
    apply propIsSet (contrImplProp ⟨x, u⟩)
  end

  -- TODO: apply “repeat” tactic
  hott def propIsProp {α : Type u} : prop (prop α) :=
  begin
    intros f g;
    apply HITs.Interval.funext; intro;
    apply HITs.Interval.funext; intro;
    apply propIsSet; assumption
  end

  hott def setIsProp {α : Type u} : prop (hset α) :=
  begin
    intros f g;
    apply HITs.Interval.funext; intro;
    apply HITs.Interval.funext; intro;
    apply HITs.Interval.funext; intro;
    apply HITs.Interval.funext; intro;
    apply setImplGroupoid; assumption
  end

  hott def ntypeIsProp : Π (n : hlevel) {α : Type u}, prop (is-n-type α)
  | −2            => contrIsProp
  | hlevel.succ n => λ p q, HITs.Interval.funext (λ x, HITs.Interval.funext (λ y, ntypeIsProp n _ _))

  hott def functionToContr {α : Type u} : prop (α → contr α) :=
  begin intros f g; apply HITs.Interval.funext; intro x; apply contrIsProp end
end

hott def retract (β : Type u) (α : Type v) :=
Σ (r : α → β) (s : β → α), r ∘ s ~ id

hott def retract.section {β : Type u} {α : Type v} (w : retract β α) : β → α := w.2.1

hott def contrRetract {α : Type u} {β : Type v} : retract β α → contr α → contr β :=
λ ⟨r, s, ε⟩ ⟨a₀, p⟩, ⟨r a₀, λ b, map r (p (s b)) ⬝ (ε b)⟩

hott def retract.path {α : Type u} {β : Type v} :
  Π (H : retract β α) {a b : β},
  retract (a = b) (H.section a = H.section b) :=
λ ⟨r, s, ε⟩ a b, ⟨λ q, (ε a)⁻¹ ⬝ (@map α β _ _ r q) ⬝ (ε b), map s,
begin
  intro p; transitivity; symmetry; apply Types.Id.assoc;
  symmetry; apply Types.Equiv.invRewriteComp;
  transitivity; apply map (· ⬝ p); apply Types.Id.invInv;
  transitivity; apply map (ε a ⬝ ·); symmetry; apply Types.Equiv.idmap;
  transitivity; apply Types.Equiv.homotopySquare ε p;
  apply map (· ⬝ ε b); apply Types.Equiv.mapOverComp
end⟩

hott def equivRespectsRetraction : Π {n : ℕ₋₂} {α : Type u} {β : Type v},
  retract β α → is-n-type α → is-n-type β
| −2            => contrRetract
| hlevel.succ n => λ G H a b, equivRespectsRetraction (retract.path G) (H _ _)

hott def equivInducesRetraction {α : Type u} {β : Type v} : α ≃ β → retract β α :=
λ ⟨f, (_, ⟨g, ε⟩)⟩, ⟨f, g, ε⟩

hott def ntypeRespectsEquiv (n : ℕ₋₂) {α : Type u} {β : Type v} :
  α ≃ β → is-n-type α → is-n-type β :=
equivRespectsRetraction ∘ equivInducesRetraction

hott def ntypeRespectsSigma : Π (n : ℕ₋₂) {α : Type u} {β : α → Type v},
  is-n-type α → (Π x, is-n-type (β x)) → is-n-type (Σ x, β x)
| −2            => λ ⟨a₀, p⟩ B, ⟨⟨a₀, (B a₀).1⟩, λ ⟨a, b⟩, Types.Sigma.prod (p a) (contrImplProp (B a) _ _)⟩
| hlevel.succ n => λ A B p q, ntypeRespectsEquiv n (Types.Equiv.symm Types.Sigma.sigmaPath)
                                (ntypeRespectsSigma n (A p.1 q.1) (λ x, B q.1 _ _))

inductive propSquash (α : Type u) : Prop
| elem : α → propSquash α

inductive Lift (α : Prop) : Type
| elem : α → Lift α

def Squash := Lift ∘ propSquash

def Squash.elem {α : Type u} : α → Squash α :=
Lift.elem ∘ propSquash.elem

def Squash.uniq {α : Type u} : Π (a b : Squash α), a = b :=
λ (Lift.elem _) (Lift.elem _), idp _

def Squash.prop {α : Type u} {β : Prop} (f : α → β) : Squash α → β :=
λ (Lift.elem (propSquash.elem x)), f x

def Squash.Lift {α : Type u} {β : Type v}
  (f : α → β) : Squash α → Squash β :=
Lift.elem ∘ Squash.prop (propSquash.elem ∘ f)

def K (α : Type u) := Π (a : α) (p : a = a), p = idp a

hott def KIffSet (α : Type u) : K α ↔ hset α :=
begin
  fapply Prod.mk;
  { intros H x y p q; induction q; apply H };
  { intros H a p; apply H }
end

hott def lemProp {α : Type u} (h : α → prop α) : prop α :=
λ a, h a a

hott def lemContr {α : Type u} (h : α → contr α) : prop α :=
λ a, contrImplProp (h a) a

def isContrFiber {α : Type u} {β : Type v} (f : α → β) :=
Π (y : β), contr (fib f y)

hott def propEquivLemma {α : Type u} {β : Type v}
  (F : prop α) (G : prop β) (f : α → β) (g : β → α) : α ≃ β :=
⟨f, (⟨g, λ _, F _ _⟩, ⟨g, λ _, G _ _⟩)⟩

hott def minusTwoEqvContr {α : Type u} : (is-(−2)-type α) ≃ contr α :=
by reflexivity

hott def minusOneEqvProp {α : Type u} : (is-(−1)-type α) ≃ prop α :=
begin
  apply propEquivLemma; apply ntypeIsProp; apply propIsProp;
  { intros H a b; exact (H a b).1 };
  { intros H a b; existsi H a b; apply propIsSet H }
end

hott def equivFunext {α : Type u} {η μ : α → Type v}
  (H : Π x, η x ≃ μ x) : (Π x, η x) ≃ (Π x, μ x) :=
begin
  existsi (λ (f : Π x, η x) (x : α), (H x).forward (f x)); apply Prod.mk;
  { existsi (λ (f : Π x, μ x) (x : α), (H x).left (f x));
    intro f; apply HITs.Interval.funext;
    intro x; apply (H x).leftForward };
  { existsi (λ (f : Π x, μ x) (x : α), (H x).right (f x));
    intro f; apply HITs.Interval.funext;
    intro x; apply (H x).forwardRight }
end

hott def zeroEqvSet {α : Type u} : (is-0-type α) ≃ hset α := calc
  (is-0-type α) ≃ (Π (x y : α), is-(−1)-type (x = y)) : by reflexivity
            ... ≃ (Π (x y : α), prop (x = y)) :
                  begin apply equivFunext; intro x;
                        apply equivFunext; intro y;
                        apply minusOneEqvProp end
            ... ≃ hset α : by reflexivity

hott def oneEqvGroupoid {α : Type u} : (is-1-type α) ≃ groupoid α := calc
  (is-1-type α) ≃ (Π (x y : α), is-0-type (x = y)) : by reflexivity
            ... ≃ (Π (x y : α), hset (x = y)) :
                   begin apply equivFunext; intro x;
                         apply equivFunext; intro y;
                         apply zeroEqvSet end
            ... ≃ groupoid α : by reflexivity

hott def propIsNType {α : Type u} (H : prop α) : Π n, is-(hlevel.succ n)-type α
| −2            => minusOneEqvProp.left H
| hlevel.succ n => hlevel.cumulative (hlevel.succ n) (propIsNType H n)

hott def hsetRespectsEquiv {α : Type u} {β : Type v} :
  α ≃ β → hset α → hset β :=
begin
  intros e H; apply zeroEqvSet.forward;
  apply ntypeRespectsEquiv 0 e;
  apply zeroEqvSet.left;
  assumption
end

hott def hsetRespectsSigma {α : Type u} {β : α → Type v}
  (H : hset α) (G : Π x, hset (β x)) : hset (Σ x, β x) :=
begin
  apply zeroEqvSet.forward; apply ntypeRespectsSigma 0;
  { apply zeroEqvSet.left; intros x y; apply H };
  { intro x; apply zeroEqvSet.left; apply G }
end

hott def propRespectsEquiv {α : Type u} {β : Type v} :
  α ≃ β → prop α → prop β :=
begin
  intros e H; apply minusOneEqvProp.forward;
  apply ntypeRespectsEquiv −1 e;
  apply minusOneEqvProp.left;
  assumption
end

hott def contrRespectsEquiv {α : Type u} {β : Type v} :
  α ≃ β → contr α → contr β :=
ntypeRespectsEquiv −2

hott def productProp {α : Type u} {β : Type v}
  (h : prop α) (g : prop β) : prop (α × β) :=
begin
  intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩;
  have p := h x₁ x₂; have q := g y₁ y₂;
  induction p; induction q; reflexivity
end

hott def prodHset {α : Type u} {β : Type v}
  (p : hset α) (q : hset β) : hset (α × β) :=
begin
  apply hsetRespectsEquiv;
  apply Types.Sigma.const;
  apply hsetRespectsSigma;
  apply p; intro x; apply q
end

hott def piProp {α : Type u} {β : α → Type v}
  (H : Π x, prop (β x)) : prop (Π x, β x) :=
λ f g, HITs.Interval.funext (λ x, H x (f x) (g x))

hott def implProp {α : Type u} {β : Type v} (H : prop β) : prop (α → β) :=
piProp (λ _, H)

hott def notIsProp {α : Type u} : prop (¬ α) :=
implProp emptyIsProp

hott def reflMereRel {α : Type u} (R : α → α → Type v) (h : Π x y, prop (R x y))
  (ρ : Π x, R x x) (f : Π x y, R x y → x = y) : hset α :=
begin
  apply (KIffSet _).left; intros a p;
  apply Types.Id.transCancelLeft (f a a (ρ a));
  transitivity; symmetry; apply Types.Equiv.transportComposition;
  transitivity; apply Types.Equiv.liftedHapply (R a); apply Types.Equiv.apd (f a) p;
  transitivity; apply map (f a a) (h _ _ _ (ρ a)); symmetry; apply Types.Id.reflRight
end

hott def doubleNegEq {α : Type u} (h : Π (x y : α), ¬¬(x = y) → x = y) : hset α :=
begin
  fapply reflMereRel;
  { intros x y; exact ¬¬(x = y) };
  { intros x y; apply implProp; apply emptyIsProp };
  { intro x; intros f; apply f; reflexivity };
  { exact h }
end

hott def lemToDoubleNeg {α : Type u} : dec α → (¬¬α → α)
| Sum.inl x => λ _, x
| Sum.inr t => λ g, Proto.Empty.elim (g t)

hott def Hedberg {α : Type u} : (Π (x y : α), dec (x = y)) → hset α :=
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
  hott def zeroPath {α β : 0-Type} (p : α.fst = β.fst) : α = β :=
  begin fapply Sigma.prod; exact p; apply ntypeIsProp end

  hott def zeroPathRefl (α : 0-Type) : @zeroPath α α Id.refl = Id.refl :=
  begin
    transitivity; apply Id.map (Sigma.prod (idp _)); change _ = Id.refl;
    apply propIsSet (ntypeIsProp 0); apply Sigma.prodRefl
  end
end

hott def Identity.ens {α : Type u} (H : hset α) : hset (Proto.Identity α) :=
begin apply hsetRespectsEquiv; apply Types.Equiv.identityEqv; assumption end

hott def zeroEquiv (α β : 0-Type) := α.1 ≃ β.1
infix:25 " ≃₀ " => zeroEquiv

end Structures

-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/tiny-library.html
-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/hsetfunext.html
def singl {α : Type u} (a : α) :=
Σ b, a = b

namespace singl
  def trivialLoop {α : Type u} (a : α) : singl a :=
  ⟨a, by reflexivity⟩

  hott def pathFromTrivialLoop {α : Type u} {a b : α}
    (r : a = b) : trivialLoop a = ⟨b, r⟩ :=
  begin induction r; reflexivity end

  hott def contr {α : Type u} (a : α) : Structures.contr (singl a) :=
  ⟨trivialLoop a, λ t, pathFromTrivialLoop t.2⟩

  hott def prop {α : Type u} (a : α) : Structures.prop (singl a) :=
  Structures.contrImplProp (contr a)
end singl

namespace Theorems
  open GroundZero.Structures GroundZero.Types.Equiv GroundZero.Types

  hott def naive {α : Type u} {β : α → Type v} {f g : Π x, β x} : f ~ g → f = g :=
  HITs.Interval.funext

  hott def weak {α : Type u} {β : α → Type v} (H : Π x, contr (β x)) : contr (Π x, β x) :=
  begin existsi (λ x, (H x).1); intro f; apply naive; intro x; apply (H x).2 end

  section
    variable {α : Type u} {β : α → Type v}

    hott def isContrSigmaHomotopy (f : Π x, β x) : contr (Σ g, f ~ g) :=
    let r (k : Π x, Σ y, f x = y) :=
    @Sigma.mk _ (λ g, f ~ g) (λ x, (k x).1) (λ x, (k x).2);
    let s (g : Π x, β x) (h : f ~ g) x :=
    Sigma.mk (g x) (h x);
    begin
      existsi Sigma.mk f (Homotopy.id f); intro ⟨g, H⟩;
      change r (λ x, Sigma.mk (f x) (idp _)) = r (s g H);
      apply Id.map r; apply contrImplProp;
      apply weak; intro x; apply singl.contr
    end

    variable (f : Π x, β x) {π : Π g (h : f ~ g), Type w} (r : π f (Homotopy.id f))
    hott def homotopyInd (g : Π x, β x) (h : f ~ g) : π g h :=
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

  hott def funext {α : Type u} {β : α → Type v}
    {f g : Π x, β x} : (f ~ g) → (f = g) :=
  @homotopyInd _ _ f (λ g x, f = g) (idp _) g

  hott def funextHapply {α : Type u} {β : α → Type v}
    {f g : Π x, β x} : funext ∘ @HITs.Interval.happly α β f g ~ id :=
  begin
    intro p; induction p; change funext (Homotopy.id _) = idp _;
    dsimp [funext]; apply homotopyIndId f
  end

  hott def happlyFunext {α : Type u} {β : α → Type v}
    (f g : Π x, β x) : HITs.Interval.happly ∘ @funext α β f g ~ id :=
  begin
    intro H; fapply @homotopyInd _ _ f (λ g G, HITs.Interval.happly (funext G) = G) _ g H;
    change _ = HITs.Interval.happly (idp _); apply Id.map HITs.Interval.happly;
    change homotopyInd _ _ _ _ = _; apply homotopyIndId
  end

  hott def full {α : Type u} {β : α → Type v} {f g : Π x, β x} : (f = g) ≃ (f ~ g) :=
  begin
    existsi HITs.Interval.happly; apply Qinv.toBiinv; existsi funext;
    apply Prod.mk; apply happlyFunext; apply funextHapply
  end

  hott def funextId {α : Type u} {β : α → Type v}
    {f : Π x, β x} : funext (Homotopy.id f) = idp f :=
  homotopyIndId _ _

  open GroundZero.Types.Equiv (transport)
  hott def mapHomotopy {α : Type u} {β : Type v} {a b : α} (f g : α → β) (p : a = b) (q : f ~ g) :
    Id.map g p = @transport (α → β) (λ h, h a = h b) f g (funext q) (Id.map f p) :=
  begin
    induction p; symmetry; transitivity; apply Types.Equiv.transportOverHmtpy;
    transitivity; apply Id.map (· ⬝ Id.map (λ (h : α → β), h a) (funext q));
    apply Id.reflRight; transitivity; symmetry; apply mapFunctoriality (λ (h : α → β), h a);
    transitivity; apply Id.map; apply Id.invComp; reflexivity
  end
end Theorems

namespace Structures
  hott def piRespectsNType :
    Π (n : ℕ₋₂) {α : Type u} {β : α → Type v},
      (Π x, is-n-type (β x)) → is-n-type (Π x, β x)
  | −2            => λ H, ⟨λ x, (H x).1, λ φ, Theorems.funext (λ x, (H x).2 (φ x))⟩
  | hlevel.succ n => λ H f g, ntypeRespectsEquiv n (Types.Equiv.symm Theorems.full)
                                (piRespectsNType n (λ x, H x _ _))

  hott def piHset {α : Type u} {β : α → Type v}
    (H : Π x, hset (β x)) : hset (Π x, β x) :=
  begin
    apply zeroEqvSet.forward; apply piRespectsNType 0;
    intro x; apply zeroEqvSet.left; apply H
  end
end Structures

hott def iter (α β : Type) : ℕ → Type
| Nat.zero   => β
| Nat.succ n => Coproduct (iter α β n) α

hott def pt := iter 𝟏

hott def vect (α : Type u) : ℕ → Type u
| Nat.zero   => 𝟏
| Nat.succ n => α × vect α n

hott def vect.const {α : Type u} (a : α) : Π n, vect α n
| Nat.zero   => ★
| Nat.succ n => (a, const a n)

hott def vect.map {α : Type u} {β : Type v} (f : α → β) :
  Π {n : ℕ}, vect α n → vect β n
| Nat.zero   => λ _, ★
| Nat.succ n => λ v, (f v.1, map f v.2)

section
  open GroundZero.Types.Equiv (transport subst)

  hott def vect.subst {α β : Type u} (p : α = β) (f : β → α) {n : ℕ} (v : vect α n) :
    vect.map f (@transport (Type u) (λ δ, vect δ n) α β p v) =
    vect.map (λ (x : α), f (transport id p x)) v :=
  begin induction p; reflexivity end
end

hott def vect.idfunc {α : Type u} : Π {n : ℕ} (f : α → α)
  (H : f ~ id) (v : vect α n), vect.map f v = v
| Nat.zero,   f, H, v => idp v
| Nat.succ n, f, H, v => Types.Product.prod (H v.1) (idfunc f H v.2)

hott def vect.id {α : Type u} {n : ℕ} (v : vect α n) : vect.map id v = v :=
begin apply vect.idfunc; reflexivity end

hott def vect.comp {α : Type u} {β : Type v} {γ : Type w} :
  Π {n : ℕ} (f : α → β) (g : β → γ) (v : vect α n), vect.map g (vect.map f v) = vect.map (g ∘ f) v
| Nat.zero,   f, g, v => idp _
| Nat.succ n, f, g, v => Types.Product.prod (idp _) (comp f g v.2)

hott def vect.constMap {α : Type u} {β : Type v} (a : α) (f : α → β) :
  Π {n : ℕ}, vect.map f (vect.const a n) = vect.const (f a) n
| Nat.zero   => idp _
| Nat.succ n => Types.Product.prod (idp _) (constMap a f)


hott def finite := iter 𝟏 𝟎
@[matchPattern] def finite.zero {n : ℕ} : finite (n + 1) := Sum.inr ★
@[matchPattern] def finite.succ {n : ℕ} : finite n → finite (n + 1) := Sum.inl

def LEMinf := Π (α : Type u), α + ¬α
notation "LEM∞" => LEMinf

open Structures (prop propset)
hott def hrel (α : Type u) := α → α → propset.{v}  

section
  variable {α : Type u} (R : hrel α)

  def isrefl  := Π a, (R a a).1
  def issymm  := Π a b, (R a b).1 → (R b a).1
  def istrans := Π a b c, (R a b).1 → (R b c).1 → (R a c).1

  def iseqrel := isrefl R × issymm R × istrans R
end

hott def eqrel (α : Type u) := Σ φ, @iseqrel α φ

-- TODO: repeat
hott def iseqrel.prop {α : Type u} {R : hrel α} : prop (iseqrel R) :=
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
  variable {α : Type u} (R : eqrel.{u, v} α)

  hott def eqrel.rel : hrel α := R.1
  hott def eqrel.iseqv : iseqrel R.rel := R.2

  hott def eqrel.apply (a b : α) : Type v :=
  (R.rel a b).1

  hott def eqrel.prop (a b : α) : prop (R.apply a b) :=
  (R.rel a b).2

  -- Accessors
  hott def eqrel.refl (a : α) : R.apply a a :=
  R.2.1 a

  hott def eqrel.symm {a b : α} : R.apply a b → R.apply b a :=
  R.2.2.1 a b

  hott def eqrel.trans {a b c : α} :
    R.apply a b → R.apply b c → R.apply a c :=
  R.2.2.2 a b c
end

hott def eqrel.eq {α : Type u} {x y : eqrel α} (p : x.rel = y.rel) : x = y :=
begin apply Types.Sigma.prod p; apply iseqrel.prop end

hott def iffOverPi {α : Type u} {β : α → Type v} {β' : α → Type w}
  (φ : Π x, β x ↔ β' x) : (Π x, β x) ↔ (Π x, β' x) :=
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
  Π X, biinv (induced η X)
end hcommSquare

hott def pullbackSquare (P : Type k) (A : Type u) (B : Type v) (C : Type w) :=
Σ (η : hcommSquare P A B C), η.isPullback

namespace Types.Equiv
  open GroundZero.Structures

  -- 1-1 correspondence
  def Corr (α : Type u) (β : Type v) :=
  Σ (R : α → β → Type w), (Π a, contr (Σ b, R a b)) × (Π b, contr (Σ a, R a b))
end Types.Equiv

end GroundZero