namespace ground_zero.proto
universes u v w

def idfun {α : Sort u} : α → α :=
λ a, a

inductive empty : Sort u
structure iff (α : Sort u) (β : Sort v) :=
(left : α → β) (right : β → α)

infix ↔ := iff

notation `𝟎` := empty
notation `𝟐` := bool

def empty.elim {α : Sort u} : empty → α.

def bottom := empty.{1}
notation `⊥` := bottom

inductive identity (α : Sort u)
| elem {} : α → identity

def identity.elim {α : Sort u} : identity α → α
| (identity.elem a) := a

def identity.lift {α : Sort u} {β : Sort v}
  (f : α → β) : identity α → identity β
| (identity.elem a) := identity.elem (f a)

def identity.lift₂ {α : Sort u} {β : Sort v} {γ : Sort w}
  (f : α → β → γ) : identity α → identity β → identity γ
| (identity.elem a) (identity.elem b) := identity.elem (f a b)

end ground_zero.proto