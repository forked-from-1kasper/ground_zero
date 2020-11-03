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
  def ring.carrier  := T.α.fst
  def ring.zero     := T.to_group.e

  def ring.neg := T.inv
  def ring.sub (x y : T.carrier) := T.φ x (T.neg y)

  def ring.isproper := T.to_group.isproper
  def ring.proper   := T.to_group.proper

  instance : has_add T.carrier := ⟨T.φ⟩
  instance : has_sub T.carrier := ⟨T.sub⟩
  instance : has_neg T.carrier := ⟨T.neg⟩

  instance : has_mul T.carrier := ⟨T.ψ⟩

  instance : has_zero T.carrier := ⟨T.zero⟩
end

@[hott] def ring.mul_zero {T : ring} (a : T.carrier) : a * 0 = 0 :=
begin
  apply group.unit_of_sqr, transitivity,
  { symmetry, apply T.distrib_left },
  apply map (T.ψ a), apply T.mul_one
end

@[hott] def ring.zero_mul {T : ring} (a : T.carrier) : 0 * a = 0 :=
begin
  apply group.unit_of_sqr, transitivity,
  { symmetry, apply T.distrib_right },
  apply map (* a), apply T.mul_one
end

@[hott] def ring.mul_neg {T : ring} (a b : T.carrier) : a * (-b) = -(a * b) :=
begin
  apply group.eq_inv_of_mul_eq_one, transitivity,
  { symmetry, apply T.distrib_left }, transitivity,
  { apply map (T.ψ a), apply group.mul_left_inv },
  apply ring.mul_zero
end

@[hott] def ring.neg_mul {T : ring} (a b : T.carrier) : (-a) * b = -(a * b) :=
begin
  apply group.eq_inv_of_mul_eq_one, transitivity,
  { symmetry, apply T.distrib_right }, transitivity,
  { apply map (* b), apply group.mul_left_inv },
  apply ring.zero_mul
end

@[hott] def ring.sub_distrib_left {T : ring} (a b c : T.carrier) := calc
  a * (b - c) = a * b + a * (-c) : T.distrib_left a b (T.neg c)
          ... = a * b - a * c    : (T.φ (T.ψ a b)) # (ring.mul_neg a c)

@[hott] def ring.sub_distrib_right {T : ring} (a b c : T.carrier) := calc
  (a - b) * c = a * c + (-b) * c : T.distrib_right a (T.neg b) c
          ... = a * c - b * c    : (T.φ (T.ψ a c)) # (ring.neg_mul b c)

class ring.assoc (T : ring) :=
(mul_assoc : Π a b c, T.ψ (T.ψ a b) c = T.ψ a (T.ψ b c))

class ring.comm (T : ring) :=
(mul_comm : Π a b, T.ψ a b = T.ψ b a)

class ring.monoid (T : ring) extends has_one T.carrier :=
(mul_one : Π a, T.ψ a one = a)
(one_mul : Π a, T.ψ a one = a)

class ring.divisible (T : ring) extends ring.monoid T :=
(inv           : T.carrier → T.carrier)
(zero          : inv 0 = 0)
(mul_inv_right : Π (x : T.carrier), T.isproper x → x * inv x = 1)

class field (T : ring) extends ring.assoc T, ring.divisible T, ring.comm T

end ground_zero.algebra