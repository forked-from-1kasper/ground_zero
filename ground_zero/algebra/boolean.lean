import ground_zero.algebra.ring

hott theory

namespace ground_zero.algebra
  class prering.boolean (T : prering) :=
  (sqr : Π (x : T.carrier), x * x = x)
end ground_zero.algebra