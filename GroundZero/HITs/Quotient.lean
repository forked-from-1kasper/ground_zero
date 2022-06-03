import GroundZero.HITs.Trunc
import GroundZero.HITs.Graph

open GroundZero.Structures
open GroundZero.Theorems
open GroundZero.Types
open GroundZero

namespace GroundZero.HITs
universe u v w u' v'

hott def Quot {α : Type u} (R : α → α → propset.{v}) := ∥Graph (λ x y, (R x y).1)∥₀

hott def Quot.elem {α : Type u} {R : α → α → propset.{v}} : α → Quot R :=
Trunc.elem ∘ Graph.elem

hott def Quot.sound {α : Type u} {R : α → α → propset.{v}} {a b : α} :
  (R a b).1 → @Id (Quot R) (Quot.elem a) (Quot.elem b) :=
begin intro H; apply Id.map Trunc.elem; apply Graph.line; assumption end

noncomputable hott def Quot.set {α : Type u} {R : α → α → propset.{v}} : hset (Quot R) :=
zeroEqvSet.forward (Trunc.uniq 0)

hott def Quot.ind {α : Type u} {R : α → α → propset.{u'}} {π : Quot R → Type v}
  (elemπ : Π x, π (Quot.elem x))
  (lineπ : Π x y H, elemπ x =[Quot.sound H] elemπ y)
  (set   : Π x, hset (π x)) : Π x, π x :=
begin
  fapply Trunc.ind;
  { fapply Graph.ind; apply elemπ;
    { intros x y H; apply Id.trans;
      apply Equiv.transportComp;
      apply lineπ } };
  { intro; apply zeroEqvSet.left; apply set }
end

attribute [eliminator] Quot.ind

hott def Quot.rec {α : Type u} {R : α → α → propset.{u'}} {β : Type v}
  (elemπ : α → β) (lineπ : Π x y, (R x y).fst → elemπ x = elemπ y) (set : hset β) : Quot R → β :=
@Quot.ind α R (λ _, β) elemπ (λ x y H, Equiv.pathoverOfEq (Quot.sound H) (lineπ x y H)) (λ _, set)

hott def Quot.lift₂ {α : Type u} {R₁ : α → α → propset.{u'}} {β : Type v} {R₂ : β → β → propset.{v'}}
  {γ : Type w} (R₁refl : Π x, (R₁ x x).fst) (R₂refl : Π x, (R₂ x x).fst) (f : α → β → γ)
  (h : hset γ) (p : Π a₁ a₂ b₁ b₂, (R₁ a₁ b₁).fst → (R₂ a₂ b₂).fst → f a₁ a₂ = f b₁ b₂) : Quot R₁ → Quot R₂ → γ :=
begin
  fapply @Quot.rec α R₁ (Quot R₂ → γ);
  { intro x; fapply Quot.rec; exact f x;
    { intros y₁ y₂ H; apply p; apply R₁refl; exact H };
    { assumption } };
  { intros x y H; apply Theorems.funext; fapply Quot.ind;
    { intro z; apply p; assumption; apply R₂refl };
    { intros; apply h };
    { intros; apply Structures.propIsSet; apply h } };
  { apply zeroEqvSet.forward; apply Structures.piRespectsNType 0;
    intros; apply zeroEqvSet.left; apply h }
end

hott def Quotient {α : Type u} (s : eqrel α) := Quot s.rel

hott def Quotient.elem {α : Type u} {s : eqrel α} : α → Quotient s :=
Quot.elem

hott def Quotient.sound {α : Type u} {s : eqrel α} {a b : α} :
  s.apply a b → @Id (Quotient s) (Quotient.elem a) (Quotient.elem b) :=
Quot.sound

noncomputable hott def Quotient.set {α : Type u} {s : eqrel α} : hset (Quotient s) :=
by apply Quot.set

hott def Quotient.ind {α : Type u} {s : eqrel α}
  {π : Quotient s → Type v}
  (elemπ : Π x, π (Quotient.elem x))
  (lineπ : Π x y H, elemπ x =[Quotient.sound H] elemπ y)
  (set   : Π x, hset (π x)) : Π x, π x :=
Quot.ind elemπ lineπ set

attribute [eliminator] Quotient.ind

hott def Quotient.indProp {α : Type u} {s : eqrel α}
  {π : Quotient s → Type v} (elemπ : Π x, π (Quotient.elem x))
  (propπ : Π x, prop (π x)) : Π x, π x :=
begin
  intro x; induction x; apply elemπ; apply propπ;
  apply Structures.propIsSet; apply propπ
end

hott def Quotient.rec {α : Type u} {β : Type v} {s : eqrel α}
  (elemπ : α → β)
  (lineπ : Π x y, s.apply x y → elemπ x = elemπ y)
  (set   : hset β) : Quotient s → β :=
by apply Quot.rec <;> assumption

hott def Quotient.lift₂ {α : Type u} {β : Type v} {γ : Type w}
  {s₁ : eqrel α} {s₂ : eqrel β} (f : α → β → γ) (h : hset γ)
  (p : Π a₁ a₂ b₁ b₂, s₁.apply a₁ b₁ → s₂.apply a₂ b₂ → f a₁ a₂ = f b₁ b₂) :
  Quotient s₁ → Quotient s₂ → γ :=
begin
  fapply Quot.lift₂; apply s₁.iseqv.fst; apply s₂.iseqv.fst;
  repeat { assumption }
end

end GroundZero.HITs