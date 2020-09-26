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

structure field :=
(G H : group)
(μ : G.carrier → H.carrier)
(η : H.carrier → G.carrier)
(incl : Π x, μ (η x) = x)
(surj : Π x, G.proper x → η (μ x) = x)
(add_comm     : Π a b, G.φ a b = G.φ b a)
(mul_comm     : Π a b, H.φ a b = H.φ b a)
(distrib_left : Π a b c, H.φ (μ a) (μ (G.φ b c)) = H.φ (μ (G.φ a b)) (μ (G.φ a c)))

end ground_zero.algebra