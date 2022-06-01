import GroundZero.Cubical.Path
open GroundZero.Cubical GroundZero.HITs

/-
  Connections as lines.
-/

namespace GroundZero.Cubical.Connection
universe u

variable {A : Type u} {a b : A} (p : Path A a b)

hott def and (i : I) : Path A a (p @ i) := <j> p @ i ∧ j
hott def or  (i : I) : Path A (p @ i) b := <j> p @ i ∨ j

end GroundZero.Cubical.Connection