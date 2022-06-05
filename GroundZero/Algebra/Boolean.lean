import GroundZero.Algebra.Ring

namespace GroundZero.Algebra
  class Prering.boolean (T : Prering) :=
  (sqr : Π (x : T.carrier), x * x = x)
end GroundZero.Algebra