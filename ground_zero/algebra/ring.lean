import ground_zero.algebra.group
open ground_zero.types.Id (map)

hott theory

namespace ground_zero.algebra

structure ring extends group :=
(ψ             : α.fst → α.fst → α.fst)
(add_comm      : Π a b, φ a b = φ b a)
(distrib_left  : Π a b c, ψ a (φ b c) = φ (ψ a b) (ψ a c))
(distrib_right : Π a b c, ψ (φ a b) c = φ (ψ a c) (ψ b c))

section
  variable (T : ring)
  def ring.carrier := T.α.fst
  def ring.zero    := T.to_group.e
  def ring.proper  := T.to_group.proper
end

class ring.assoc (T : ring) :=
(mul_assoc : Π a b c, T.ψ (T.ψ a b) c = T.ψ a (T.ψ b c))

class ring.comm (T : ring) :=
(mul_comm : Π a b, T.ψ a b = T.ψ b a)

class ring.identity (T : ring) :=
(idm      : T.carrier)
(mul_unit : Π x, T.proper x → T.ψ x idm = x)
(unit_mul : Π x, T.proper x → T.ψ idm x = x)

class ring.invertible (T : ring) extends ring.identity T :=
(inv           : T.carrier → T.carrier)
(inv_zero      : inv T.zero = T.zero)
(mul_inv_right : Π x, T.proper x → T.ψ x (inv x) = idm)

class field (T : ring) extends ring.assoc T, ring.comm T, ring.invertible T

end ground_zero.algebra