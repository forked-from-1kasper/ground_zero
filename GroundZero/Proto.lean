import GroundZero.Meta.Basic

namespace GroundZero.Proto
universe u v w

hott def idfun {α : Sort u} : α → α :=
(a ↦ a)

inductive Empty : Type u

structure Iff (α : Sort u) (β : Sort v) :=
(left : α → β) (right : β → α)

infix:30 (priority := high) " ↔ " => Iff

hott def Iff.refl {α : Sort u} : α ↔ α :=
⟨idfun, idfun⟩

hott def Iff.symm {α : Sort u} {β : Sort v} : (α ↔ β) → (β ↔ α) :=
λ p, ⟨p.right, p.left⟩

hott def Iff.comp {α : Sort u} {β : Sort v} {γ : Sort w} :
  (α ↔ β) → (β ↔ γ) → (α ↔ γ) :=
λ p q, ⟨q.left ∘ p.left, p.right ∘ q.right⟩

instance : @Reflexive  (Sort u) Iff := ⟨@Iff.refl⟩
instance : @Symmetric  (Sort u) Iff := ⟨@Iff.symm⟩
instance : @Transitive (Sort u) Iff := ⟨@Iff.comp⟩

notation "𝟎" => Empty
notation "𝟐" => Bool
notation "ℕ" => Nat

def Empty.elim {α : Sort u} (xs : Empty) : α :=
nomatch xs

def Bool.elim {α : Sort u} : α → α → 𝟐 → α :=
λ b₁ b₂ b, @Bool.casesOn (λ _, α) b b₁ b₂

def Bottom := Empty.{0}
notation (priority := low) "⊥" => Bottom

inductive Identity (α : Type u)
| elem : α → Identity α

def Identity.elim {α : Type u} : Identity α → α
| Identity.elem a => a

def Identity.lift {α : Type u} {β : Type v}
  (f : α → β) : Identity α → Identity β
| Identity.elem a => Identity.elem (f a)

def Identity.lift₂ {α : Type u} {β : Type v} {γ : Type w}
  (f : α → β → γ) : Identity α → Identity β → Identity γ
| Identity.elem a, Identity.elem b => Identity.elem (f a b)

end GroundZero.Proto
