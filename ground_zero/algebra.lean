import ground_zero.HITs.ntrunc
open ground_zero.types.eq (pointed)
open ground_zero.structures (hset)

hott theory

namespace ground_zero.algebra

universes u v
class magma (α : Type u) :=
(mul : α → α → α)

infix ` · `:70 := magma.mul

class pointed_magma (α : Type u) extends magma α :=
(e : α)

class monoid (α : Type u) extends magma α :=
(truncation : hset α) (e : α)
(right_unit : Π (x : α), x · e = x)
(left_unit : Π (x : α), e · x = x)
(assoc : Π (x y z : α), x · (y · z) = (x · y) · z)

class group (α : Type u) extends monoid α :=
(inv : α → α)
(right_inv : Π (x : α), x · inv x = e)
(left_inv : Π (x : α), inv x · x = e)

def e {α : Type u} [group α] : α := monoid.e α
instance {α : Type u} [monoid α] : has_one α := ⟨monoid.e α⟩
instance {α : Type u} [group α] : has_inv α := ⟨group.inv⟩

theorem group_unit_is_unique {α : Type u} [group α] (e' : α)
  (right_unit' : Π x, x · e' = x)
  (left_unit' : Π x, e' · x = x)
  (H : e = e' → empty) : empty := begin
  have p := monoid.right_unit e',
  have q := left_unit' e,
  exact H (q⁻¹ ⬝ p)
end

theorem square_is_unique {α : Type u} [group α] (x : α)
  (h : x · x = x) : x = 1 := calc
    x = e · x : begin symmetry, apply monoid.left_unit end
  ... = (x⁻¹ · x) · x :
        begin
          apply ground_zero.types.eq.map (· x),
          symmetry, apply group.left_inv x
        end
  ... = x⁻¹ · (x · x) : begin symmetry, apply monoid.assoc end
  ... = x⁻¹ · x : magma.mul x⁻¹ # h
  ... = 1 : by apply group.left_inv

theorem inv_of_inv {α : Type u} [group α] (x : α) : (x⁻¹)⁻¹ = x := calc
  (x⁻¹)⁻¹ = e · (x⁻¹)⁻¹ : begin symmetry, apply monoid.left_unit end
      ... = (x · x⁻¹) · (x⁻¹)⁻¹ :
            begin
              apply ground_zero.types.eq.map (· x⁻¹⁻¹),
              symmetry,
              apply group.right_inv x
            end
      ... = x · (x⁻¹ · x⁻¹⁻¹) : begin symmetry, apply monoid.assoc end
      ... = x · e : magma.mul x # (group.right_inv x⁻¹)
      ... = x : monoid.right_unit x

theorem reduce_left {α : Type u} [group α] (a b c : α)
  (h : c · a = c · b) : a = b := calc
    a = e · a         : (monoid.left_unit a)⁻¹
  ... = (c⁻¹ · c) · a : (· a) # (group.left_inv c)⁻¹
  ... = c⁻¹ · (c · a) : begin symmetry, apply monoid.assoc end
  ... = c⁻¹ · (c · b) : magma.mul c⁻¹ # h
  ... = (c⁻¹ · c) · b : by apply monoid.assoc
  ... = e · b         : (· b) # (group.left_inv c)
  ... = b             : monoid.left_unit b

theorem identity_inv {α : Type u} [group α] : e = e⁻¹ :> α :=
(group.right_inv e)⁻¹ ⬝ monoid.left_unit e⁻¹

def Zentrum (α : Type u) [group α] :=
Σ (z : α), Π g, z · g = g · z

def commutator {α : Type u} [group α] (g h : α) :=
g⁻¹ · h⁻¹ · g · h

section
  variables {α : Type u} {β : Type v} [group α] [group β]

  def is_homo (φ : α → β) :=
  Π a b, φ (a · b) = φ a · φ b

  def Ker (φ : α → β) (H : is_homo φ) := Σ g, φ g = e
  def Im (φ : α → β) (H : is_homo φ) := Σ g f, φ g = f
end

prefix ⁻¹ := group.inv

def coeffspace (α : Type u) (β : Type v) :=
β → α → α

def is_eigenvalue {α : Type u} {β : Type v}
  (mul : coeffspace α β) (A : α → α) (x : α) :=
Σ y, A x = mul y x

def spectrum {α : Type u} {β : Type v}
  (mul : coeffspace α β) (A : α → α) :=
Σ x, is_eigenvalue mul A x

--def homotopy_group (X : pointed) (n : ℕ) := ∥Ω[n], X∥₀
--notation `π[` n `]` `, ` X := homotopy_group X n

end ground_zero.algebra