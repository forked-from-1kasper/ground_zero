import ground_zero.algebra.group
open ground_zero.types.Id (map)

hott theory

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
(distrib_left : Π a b c,
  η (H.φ (μ a) (μ (G.φ b c))) = G.φ (η (H.φ (μ a) (μ b))) (η (H.φ (μ a) (μ c))))

def field.carrier (F : field) := F.G.carrier

def field.add (F : field) : F.carrier → F.carrier → F.carrier := F.G.φ
def field.mul (F : field) (x y : F.carrier) : F.carrier :=
F.η (F.H.φ (F.μ x) (F.μ y))

def field.distrib_right (F : field) (a b c : F.carrier) :
  F.mul (F.add a b) c = F.add (F.mul a c) (F.mul b c) := begin
  transitivity, { apply map F.η, apply F.mul_comm },
  transitivity, { apply F.distrib_left },
  apply ground_zero.types.equiv.bimap; apply map F.η; apply F.mul_comm
end

def field.to_ring (F : field) : ring :=
⟨F.G, F.mul, F.add_comm, F.distrib_left, F.distrib_right⟩

end ground_zero.algebra