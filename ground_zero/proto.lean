namespace ground_zero.proto
universes u v

structure iff (α : Sort u) (β : Sort v) :=
(left : α → β) (right : β → α)

infix ↔ := iff

end ground_zero.proto