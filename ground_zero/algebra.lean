import ground_zero.HITs.ntrunc
open ground_zero.types.eq (pointed)
open ground_zero.structures (hset)

hott theory

namespace ground_zero.algebra

universes u v
class magma (α : Type u) :=
(m : α → α → α)

class pointed_magma (α : Type u) extends magma α :=
(e : α)

class monoid (α : Type u) :=
(truncation : hset α)
(mul : α → α → α) (e : α)
(left_unit : Π (x : α), mul x e = x)
(right_unit : Π (x : α), mul e x = x)
(assoc : Π (x y z : α), mul x (mul y z) = mul (mul x y) z)

infix ` · `:70 := monoid.mul

class group (α : Type u) extends monoid α :=
(inv : α → α)
(left_inv : Π (x : α), x · (inv x) = e)
(right_inv : Π (x : α), (inv x) · x = e)

def e {α : Type u} [group α] : α := monoid.e α

theorem group_unit_is_unique {α : Type u} [group α] (e' : α)
  (left_unit' : Π x, x · e' = x)
  (right_unit' : Π x, e' · x = x)
  (H : e = e' → empty) : empty := begin
  have p := monoid.left_unit e',
  have q := right_unit' e,
  exact H (q⁻¹ ⬝ p)
end

section
  variables {α : Type u} {β : Type v} [group α] [group β]

  def is_homo (φ : α → β) :=
  Π a b, φ (a · b) = φ a · φ b

  def Ker (φ : α → β) (H : is_homo φ) := Σ g, φ g = e
  def Im (φ : α → β) (H : is_homo φ) := Σ g f, φ g = f
end

prefix ⁻¹ := group.inv

--def homotopy_group (X : pointed) (n : ℕ) := ∥Ω[n], X∥₀
--notation `π[` n `]` `, ` X := homotopy_group X n

end ground_zero.algebra