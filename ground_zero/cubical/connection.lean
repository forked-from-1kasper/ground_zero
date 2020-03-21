import ground_zero.cubical.path
open ground_zero.cubical ground_zero.HITs

/-
  Connections as lines.
-/

namespace ground_zero.cubical.connection
universe u

@[hott] def and {α : Type u} {a b : α} (p : a ⇝ b) (i : I) : a ⇝ p # i :=
<j> p # i ∧ j

@[hott] def or {α : Type u} {a b : α} (p : a ⇝ b) (i : I) : p # i ⇝ b :=
<j> p # i ∨ j

end ground_zero.cubical.connection