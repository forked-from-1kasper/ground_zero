import ground_zero.structures ground_zero.types.integer
open ground_zero.types.eq (pointed)
open ground_zero.structures (hset)
open ground_zero.types

hott theory

namespace ground_zero.algebra

universes u v
class magma (α : Type u) :=
(mul : α → α → α)

infixr ` · `:70 := magma.mul

class pointed_magma (α : Type u) extends magma α :=
(e {} : α)
open pointed_magma

class monoid (α : Type u) extends pointed_magma α :=
(right_unit : Π (x : α), x · e = x)
(left_unit : Π (x : α), e · x = x)
(assoc : Π (x y z : α), x · (y · z) = (x · y) · z)

class abelian (α : Type u) [magma α] :=
(comm : Π (x y : α), x · y = y · x)

class group (α : Type u) extends monoid α :=
(inv : α → α)
(right_inv : Π (x : α), x · inv x = e)
(left_inv : Π (x : α), inv x · x = e)

instance {α : Type u} [pointed_magma α] : has_one α := ⟨e⟩
instance {α : Type u} [group α] : has_inv α := ⟨group.inv⟩

def group.natural_pow {α : Type u} [group α] (x : α) : ℕ → α
| 0 := 1
| (n + 1) := x · group.natural_pow n

def group.pow {α : Type u} [group α] (x : α) : integer → α
| (integer.pos n) := group.natural_pow x n
| (integer.neg n) := group.natural_pow x⁻¹ (n + 1)

section
  variables {α : Type u} [group α]
  instance nat_pow : has_pow α ℕ := ⟨group.natural_pow⟩
  instance int_pow : has_pow α integer := ⟨group.pow⟩
end

namespace bool
  instance : magma bool := ⟨bxor⟩
  instance : pointed_magma bool := ⟨ff⟩

  instance : monoid bool :=
  { right_unit := begin intro x, cases x; reflexivity end,
    left_unit := begin intro x, cases x; reflexivity end,
    assoc := begin intros x y z, cases x; cases y; cases z; reflexivity end }

  instance : group bool :=
  { inv := id,
    left_inv := begin intro x, cases x; reflexivity end,
    right_inv := begin intro x, cases x; reflexivity end }
end bool

namespace unit
  instance : magma 𝟏 := ⟨λ x y, x⟩
  instance : pointed_magma 𝟏 := ⟨★⟩

  instance : monoid 𝟏 :=
  { right_unit := begin intro x, cases x; reflexivity end,
    left_unit := begin intro x, cases x; reflexivity end,
    assoc := begin intros x y z, cases x; cases y; cases z; reflexivity end }

  instance : group 𝟏 :=
  { inv := id,
    left_inv := begin intro x, cases x; reflexivity end,
    right_inv := begin intro x, cases x; reflexivity end }
end unit

end ground_zero.algebra