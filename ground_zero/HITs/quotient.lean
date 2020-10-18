import ground_zero.HITs.trunc ground_zero.HITs.graph
open ground_zero.structures (propset prop hset zero_eqv_set)
open ground_zero.theorems (funext)
open ground_zero

namespace ground_zero.HITs
universes u v w u' v'

hott theory

def quot {α : Type u} (R : α → α → propset.{v}) := ∥graph (λ x y, (R x y).fst)∥₀

@[hott] def quot.elem {α : Type u} {R : α → α → propset.{v}} : α → quot R :=
trunc.elem ∘ graph.elem

@[hott] def quot.sound {α : Type u} {R : α → α → propset.{v}} {a b : α} :
  (R a b).fst → quot.elem a = quot.elem b :> quot R :=
begin
  intro H, apply ground_zero.types.Id.map trunc.elem,
  apply graph.line, assumption
end

@[hott] noncomputable def quot.set {α : Type u} {R : α → α → propset.{v}} : hset (quot R) :=
λ _ _, zero_eqv_set.forward (trunc.uniq 0)

@[hott] def quot.ind {α : Type u} {R : α → α → propset.{u'}}
  {π : quot R → Type v}
  (elemπ : Π x, π (quot.elem x))
  (lineπ : Π x y H, elemπ x =[quot.sound H] elemπ y)
  (set   : Π x, hset (π x)) : Π x, π x :=
begin
  fapply trunc.ind,
  { fapply graph.ind, apply elemπ,
    { intros x y H, apply ground_zero.types.Id.trans,
      apply ground_zero.types.equiv.transport_comp,
      apply lineπ } },
  { intro x, apply zero_eqv_set.left, apply set }
end

@[hott] def quot.rec {α : Type u} {β : Type v} {R : α → α → propset.{u'}}
  (elemπ : α → β)
  (lineπ : Π x y, (R x y).fst → elemπ x = elemπ y)
  (set   : hset β) : quot R → β :=
@quot.ind α R (λ _, β) elemπ
  (λ x y H, ground_zero.types.equiv.pathover_of_eq (quot.sound H) (lineπ x y H))
  (λ _ _ _, set)

@[hott] def quot.lift₂ {α : Type u} {β : Type v} {γ : Type w}
  {R₁ : α → α → propset.{u'}} {R₂ : β → β → propset.{v'}}
  (R₁refl : Π x, (R₁ x x).fst) (R₂refl : Π x, (R₂ x x).fst) (f : α → β → γ)
  (h : hset γ) (p : Π a₁ a₂ b₁ b₂, (R₁ a₁ b₁).fst → (R₂ a₂ b₂).fst → f a₁ a₂ = f b₁ b₂) :
  quot R₁ → quot R₂ → γ :=
begin
  intro x, fapply quot.rec _ _ _ x; clear x,
  { intros x y, fapply quot.rec _ _ _ y; clear y,
    { intro y, exact f x y },
    { intros y₁ y₂ H, apply p, apply R₁refl,
      exact H },
    { assumption } },
  { intros x y H, apply ground_zero.theorems.funext,
    fapply quot.ind,
    { intro z, apply p, assumption, apply R₂refl },
    { intros, apply h },
    { intros, apply ground_zero.structures.prop_is_set,
      apply h } },
  { apply zero_eqv_set.forward,
    apply ground_zero.structures.pi_respects_ntype 0,
    intros, apply zero_eqv_set.left, intros a b p q, apply h }
end

def quotient {α : Type u} (s : eqrel α) := quot s.rel

@[hott] def quotient.elem {α : Type u} {s : eqrel α} : α → quotient s :=
quot.elem

@[hott] def quotient.sound {α : Type u} {s : eqrel α} {a b : α} :
  s.apply a b → quotient.elem a = quotient.elem b :=
quot.sound

@[hott] noncomputable def quotient.set {α : Type u} {s : eqrel α} : hset (quotient s) :=
by apply quot.set

@[hott] def quotient.ind {α : Type u} {s : eqrel α}
  {π : quotient s → Type v}
  (elemπ : Π x, π (quotient.elem x))
  (lineπ : Π x y H, elemπ x =[quotient.sound H] elemπ y)
  (set   : Π x, hset (π x)) : Π x, π x :=
quot.ind elemπ lineπ set

@[hott] def quotient.ind_prop {α : Type u} {s : eqrel α}
  {π : quotient s → Type v}
  (elemπ : Π x, π (quotient.elem x))
  (propπ : Π x, prop (π x)) : Π x, π x :=
begin
  fapply quotient.ind,
  { exact elemπ },
  { intros, change _ = _, apply propπ },
  { intros, apply ground_zero.structures.prop_is_set,
    apply propπ }
end

@[hott] def quotient.rec {α : Type u} {β : Type v} {s : eqrel α}
  (elemπ : α → β)
  (lineπ : Π x y, s.apply x y → elemπ x = elemπ y)
  (set   : hset β) : quotient s → β :=
by apply quot.rec; assumption

@[hott] def quotient.lift₂ {α : Type u} {β : Type v} {γ : Type w}
  {s₁ : eqrel α} {s₂ : eqrel β} (f : α → β → γ) (h : hset γ)
  (p : Π a₁ a₂ b₁ b₂, s₁.apply a₁ b₁ → s₂.apply a₂ b₂ → f a₁ a₂ = f b₁ b₂) :
  quotient s₁ → quotient s₂ → γ :=
begin
  fapply quot.lift₂, apply s₁.iseqv.fst, apply s₂.iseqv.fst,
  repeat { assumption }
end

end ground_zero.HITs