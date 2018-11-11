import ground_zero.ntrunc
open ground_zero.eq (pointed)
open ground_zero.structures (hset)

namespace ground_zero.algebra

universe u
class magma (α : Type u) :=
(m : α → α → α)

class pointed_magma (α : Type u) extends magma α :=
(e : α)

class monoid (α : Type u) extends hset α :=
(mul : α → α → α) (e : α)
(left_unit : Π (x : α), mul x e = x :> α)
(right_unit : Π (x : α), mul e x = x :> α)
(assoc : Π (x y z : α), mul x (mul y z) = mul (mul x y) z :> α)

infix ` · `:50 := monoid.mul

class group (α : Type u) extends monoid α :=
(inv : α → α)
(left_inv : Π (x : α), x · (inv x) = e :> α)
(right_inv : Π (x : α), (inv x) · x = e :> α)

prefix ⁻¹ := group.inv

def homotopy_group (X : pointed) (n : ℕ) := ∥Ω[n], X∥₀
notation `π[` n `]` `, ` X := homotopy_group X n

instance first_hset (X : pointed) : hset (π[1], X) := ⟨{!!}⟩

end ground_zero.algebra