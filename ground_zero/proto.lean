namespace ground_zero.proto
universes u v

def idfun {α : Sort u} : α → α :=
λ a, a

inductive empty : Sort u
structure iff (α : Sort u) (β : Sort v) :=
(left : α → β) (right : β → α)

infix ↔ := iff

notation [parsing_only] `𝟎` := empty
notation [parsing_only] `𝟐` := bool

def empty.elim {α : Sort u} : empty → α.

end ground_zero.proto