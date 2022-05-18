import ground_zero.cubical.path
open ground_zero.cubical ground_zero.HITs

/-
  Connections as lines.
-/

namespace ground_zero.cubical.connection
universe u

variables {A : Type u} {a b : A} (p : Path A a b)

@[hott] def and (i : I) : Path A a (p # i) := <j> p # i ∧ j
@[hott] def or  (i : I) : Path A (p # i) b := <j> p # i ∨ j

end ground_zero.cubical.connection