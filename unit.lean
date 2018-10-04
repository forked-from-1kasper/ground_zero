namespace ground_zero

universe u
inductive unit : Sort u
| star : unit

notation [parsing_only] `★` := unit.star

namespace unit
  def elim {α : Sort u} (a : α) : unit → α
  | star := a
end unit

end ground_zero