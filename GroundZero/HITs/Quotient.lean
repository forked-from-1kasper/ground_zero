import GroundZero.HITs.Trunc

open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Theorems
open GroundZero.Types
open GroundZero

namespace GroundZero.HITs
universe u v w u' v' w'

hott definition Setquot {A : Type u} (R : A → A → Prop v) := ∥Quotient (λ x y, (R x y).1)∥₀

hott definition Setquot.elem {A : Type u} {R : A → A → Prop v} : A → Setquot R :=
Trunc.elem ∘ Quotient.elem

hott definition Setquot.sound {A : Type u} {R : A → A → Prop v} {a b : A} :
  (R a b).1 → @Id (Setquot R) (Setquot.elem a) (Setquot.elem b) :=
begin intro; dsimp [elem]; apply ap Trunc.elem; apply Quotient.line; assumption end

hott lemma Setquot.set {A : Type u} {R : A → A → Prop v} : hset (Setquot R) :=
zeroEqvSet.forward (Trunc.uniq 0)

hott definition Setquot.ind {A : Type u} {R : A → A → Prop u'} {π : Setquot R → Type v}
  (elemπ : Π x, π (Setquot.elem x))
  (lineπ : Π x y H, elemπ x =[Setquot.sound H] elemπ y)
  (set   : Π x, hset (π x)) : Π x, π x :=
begin
  fapply Trunc.ind;
  { fapply Quotient.ind; apply elemπ;
    { intros x y H; apply Id.trans;
      apply transportComp;
      apply lineπ } };
  { intro; apply zeroEqvSet.left; apply set }
end

attribute [eliminator] Setquot.ind

hott definition Setquot.rec {A : Type u} {R : A → A → Prop u'} {B : Type v}
  (elemπ : A → B) (lineπ : Π x y, (R x y).fst → elemπ x = elemπ y) (set : hset B) : Setquot R → B :=
@Setquot.ind A R (λ _, B) elemπ (λ x y H, pathoverOfEq (Setquot.sound H) (lineπ x y H)) (λ _, set)

hott definition Setquot.lift₂ {A : Type u} {R₁ : A → A → Prop u'} {B : Type v} {R₂ : B → B → Prop v'}
  {γ : Type w} (R₁refl : Π x, (R₁ x x).fst) (R₂refl : Π x, (R₂ x x).fst) (f : A → B → γ)
  (h : hset γ) (p : Π a₁ a₂ b₁ b₂, (R₁ a₁ b₁).fst → (R₂ a₂ b₂).fst → f a₁ a₂ = f b₁ b₂) : Setquot R₁ → Setquot R₂ → γ :=
begin
  fapply @Setquot.rec A R₁ (Setquot R₂ → γ);
  { intro x; fapply Setquot.rec; exact f x;
    { intros y₁ y₂ H; apply p; apply R₁refl; exact H };
    { assumption } };
  { intros x y H; apply Theorems.funext; fapply Setquot.ind;
    { intro z; apply p; assumption; apply R₂refl };
    { intros; apply h };
    { intros; apply Structures.propIsSet; apply h } };
  { apply zeroEqvSet.forward; apply Structures.piRespectsNType 0;
    intros; apply zeroEqvSet.left; apply h }
end

hott definition Relquot {A : Type u} (s : eqrel A) := Setquot s.rel

hott definition Relquot.elem {A : Type u} {s : eqrel A} : A → Relquot s :=
Setquot.elem

hott definition Relquot.sound {A : Type u} {s : eqrel A} {a b : A} :
  s.apply a b → @Id (Relquot s) (Relquot.elem a) (Relquot.elem b) :=
Setquot.sound

hott corollary Relquot.set {A : Type u} {s : eqrel A} : hset (Relquot s) :=
by apply Setquot.set

hott definition Relquot.ind {A : Type u} {s : eqrel A}
  {π : Relquot s → Type v}
  (elemπ : Π x, π (Relquot.elem x))
  (lineπ : Π x y H, elemπ x =[Relquot.sound H] elemπ y)
  (set   : Π x, hset (π x)) : Π x, π x :=
Setquot.ind elemπ lineπ set

attribute [eliminator] Relquot.ind

hott definition Relquot.indProp {A : Type u} {s : eqrel A}
  {π : Relquot s → Type v} (elemπ : Π x, π (Relquot.elem x))
  (propπ : Π x, prop (π x)) : Π x, π x :=
begin
  intro x; induction x; apply elemπ; apply propπ;
  apply Structures.propIsSet; apply propπ
end

hott definition Relquot.rec {A : Type u} {B : Type v} {s : eqrel A}
  (elemπ : A → B)
  (lineπ : Π x y, s.apply x y → elemπ x = elemπ y)
  (set   : hset B) : Relquot s → B :=
by apply Setquot.rec <;> assumption

hott definition Relquot.lift₂ {A : Type u} {B : Type v} {γ : Type w}
  {s₁ : eqrel A} {s₂ : eqrel B} (f : A → B → γ) (h : hset γ)
  (p : Π a₁ a₂ b₁ b₂, s₁.apply a₁ b₁ → s₂.apply a₂ b₂ → f a₁ a₂ = f b₁ b₂) :
  Relquot s₁ → Relquot s₂ → γ :=
begin
  fapply Setquot.lift₂; apply s₁.iseqv.fst; apply s₂.iseqv.fst;
  repeat { assumption }
end

end GroundZero.HITs
