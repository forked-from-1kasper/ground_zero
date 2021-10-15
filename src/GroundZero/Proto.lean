import GroundZero.Meta.Notation

namespace GroundZero.Proto
universe u v w

def idfun {α : Sort u} : α → α :=
(a ↦ a)

inductive Empty : Type u

structure Iff (α : Sort u) (β : Sort v) :=
(left : α → β) (right : β → α)

infix:30 " ↔ " => Iff

notation "𝟎" => Empty
notation "𝟐" => Bool

def Empty.elim {α : Sort u} (xs : Empty) : α :=
nomatch xs

inductive Identity (α : Type u)
| elem {} : α → Identity α

def Identity.elim {α : Type u} : Identity α → α
| Identity.elem a => a

def Identity.lift {α : Type u} {β : Type v}
  (f : α → β) : Identity α → Identity β
| Identity.elem a => Identity.elem (f a)

def Identity.lift₂ {α : Type u} {β : Type v} {γ : Type w}
  (f : α → β → γ) : Identity α → Identity β → Identity γ
| Identity.elem a, Identity.elem b => Identity.elem (f a b)

end GroundZero.Proto