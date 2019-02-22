import ground_zero.cubical.path
open ground_zero.cubical ground_zero.HITs

/-
  Connections as lines.
-/

namespace ground_zero.cubical.connection
universe u

def and {α : Sort u} {a b : α} (p : a ⇝ b) (i : I) : a ⇝ p # i :=
<j> p # i ∧ j

def or {α : Sort u} {a b : α} (p : a ⇝ b) (i : I) : p # i ⇝ b :=
<j> p # i ∨ j

end ground_zero.cubical.connection