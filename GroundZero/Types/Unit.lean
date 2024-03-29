import GroundZero.Types.Equiv

namespace GroundZero.Types
universe u

inductive Unit : Type u
| star : Unit

attribute [induction_eliminator] Unit.casesOn

notation "𝟏" => Unit
notation "★" => Unit.star

namespace Unit
  hott definition elim {A : Type u} (a : A) : 𝟏 → A := λ ★, a

  hott definition ind {B : 𝟏 → Type u} (g : B ★) : Π x, B x := λ ★, g

  hott definition uniq : Π x, x = ★ := λ ★, idp ★
end Unit

end GroundZero.Types
