namespace ground_zero.proto
universes u v

inductive empty : Sort u
structure iff (α : Sort u) (β : Sort v) :=
(left : α → β) (right : β → α)

infix ↔ := iff

notation [parsing_only] `𝟎` := empty
notation [parsing_only] `𝟐` := bool

end ground_zero.proto