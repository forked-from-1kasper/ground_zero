import GroundZero.Types.Equiv

namespace GroundZero.Types
universe u

inductive Unit : Type u
| star : Unit

attribute [eliminator] Unit.casesOn

notation "𝟏" => Unit
notation "★" => Unit.star

namespace Unit
  hott def elim {A : Type u} (a : A) : 𝟏 → A := λ ★, a
  hott def ind {B : 𝟏 → Type u} (g : B ★) : Π x, B x := λ ★, g
  hott def uniq : Π x, x = ★ := λ ★, idp ★
end Unit

end GroundZero.Types