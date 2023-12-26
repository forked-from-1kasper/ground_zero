import GroundZero.Cubical.Path
open GroundZero.Cubical GroundZero.HITs

/-
  Connections as lines.
-/

namespace GroundZero.Cubical.Connection
universe u

variable {A : Type u} {a b : A} (p : Path A a b)

hott definition and (i : I) : Path A a (p @ i) := <j> p @ i ∧ j
hott definition or  (i : I) : Path A (p @ i) b := <j> p @ i ∨ j

end GroundZero.Cubical.Connection
