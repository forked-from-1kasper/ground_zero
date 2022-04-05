import ground_zero.types.equiv

namespace ground_zero.types

universe u

@[hott] def uninhabited_type {α : Type u} (f : α → empty) : α ≃ empty :=
begin
  have g : empty → α := begin intro e, induction e end,
  existsi f, split; existsi g,
  { intro x, have e := f x, induction e },
  { intro x, induction x }
end

inductive lost (α : Type u)
| cons {} : α → lost → lost

namespace lost

@[hott] def code {α : Type u} : lost α → empty
| (lost.cons head tail) := code tail

@[hott] def is_zero {α : Type u} : lost α ≃ empty :=
uninhabited_type code

end lost

end ground_zero.types