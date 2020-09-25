import ground_zero.algebra.group

namespace ground_zero.algebra

structure ring extends group :=
(ψ             : α.fst → α.fst → α.fst)
(add_comm      : Π a b, φ a b = φ b a)
(distrib_left  : Π a b c, ψ a (φ b c) = φ (ψ a b) (ψ a c))
(distrib_right : Π a b c, ψ (φ a b) c = φ (ψ a c) (ψ b c))

def ring.carrier (T : ring) := T.α.fst

@[class] def ring.assoc (T : ring) :=
Π a b c, T.ψ (T.ψ a b) c = T.ψ a (T.ψ b c)

@[class] def ring.comm (T : ring) :=
Π a b, T.ψ a b = T.ψ b a

class ring.identity (T : ring) :=
(id       : T.carrier)
(mul_unit : Π x, T.ψ x id = x)
(unit_mul : Π x, T.ψ id x = x)

end ground_zero.algebra