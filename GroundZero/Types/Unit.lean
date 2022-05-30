import GroundZero.Types.Equiv

namespace GroundZero.Types
universe u

inductive Unit : Type u
| star : Unit

attribute [eliminator] Unit.casesOn

notation "𝟏" => Unit
notation "★" => Unit.star

namespace Unit
  hott def elim {α : Type u} (a : α) : 𝟏 → α := λ ★, a
  hott def ind {π : 𝟏 → Type u} (g : π ★) : Π x, π x := λ ★, g
  hott def uniq : Π x, x = ★ := λ ★, idp ★
end Unit

end GroundZero.Types