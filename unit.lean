import ground_zero.equiv

namespace ground_zero

universe u
inductive unit : Sort u
| star : unit

notation [parsing_only] `★` := unit.star

namespace unit
  def elim {α : Sort u} (a : α) : unit → α
  | star := a

  def ind {π : unit → Sort u} (g : π star) : Π (x : unit), π x
  | star := g

  def uniq : Π (x : unit), x = star :> _
  | star := eq.refl star
end unit

end ground_zero