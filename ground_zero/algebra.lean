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

theorem group_unit_is_unique {α : Type u} [group α] (e' : α)
  (right_unit' : Π x, x · e' = x)
  (left_unit' : Π x, e' · x = x)
  (H : e = e' → empty) : empty := begin
  have p := monoid.right_unit e',
  have q := left_unit' e,
  exact H (q⁻¹ ⬝ p)
end

section
  variables {α : Type u} [group α]

  theorem square_is_unique (x : α)
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
  
  theorem inv_of_inv (x : α) : (x⁻¹)⁻¹ = x := calc
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
  
  theorem reduce_left (a b c : α)
    (h : c · a = c · b) : a = b := calc
      a = e · a         : (monoid.left_unit a)⁻¹
    ... = (c⁻¹ · c) · a : (· a) # (group.left_inv c)⁻¹
    ... = c⁻¹ · (c · a) : begin symmetry, apply monoid.assoc end
    ... = c⁻¹ · (c · b) : magma.mul c⁻¹ # h
    ... = (c⁻¹ · c) · b : by apply monoid.assoc
    ... = e · b         : (· b) # (group.left_inv c)
    ... = b             : monoid.left_unit b

  theorem identity_inv : 1 = 1⁻¹ :> α :=
  (group.right_inv e)⁻¹ ⬝ monoid.left_unit e⁻¹

  theorem identity_sqr : 1 = 1 · 1 :> α :=
  (monoid.left_unit 1)⁻¹
end

def commutes {α : Type u} [group α] (x y : α) :=
x · y = y · x

def Zentrum (α : Type u) [group α] :=
Σ (z : α), Π g, commutes z g

def commutator {α : Type u} [group α] (g h : α) :=
g⁻¹ · h⁻¹ · g · h

def conjugate {α : Type u} [group α] (a x : α) :=
x⁻¹ · a · x

section
  variables {α : Type u} {β : Type v} [group α] [group β]

  def is_homo (φ : α → β) :=
  Π a b, φ (a · b) = φ a · φ b

  def homo (α : Type u) (β : Type v) [group α] [group β] :=
  Σ (φ : α → β), is_homo φ

  def ker (φ : homo α β) (g : α) := φ.fst g = 1
  def Ker (φ : homo α β) := Σ g, ker φ g

  def Im (φ : homo α β) := Σ g f, φ.fst g = f
end

structure is_subgroup {α : Type u} [group α] (φ : α → Type v) :=
(unit : φ 1)
(mul : Π a b, φ a → φ b → φ (a · b))
(inv : Π a, φ a → φ a⁻¹)

def is_normal_subgroup {α : Type u} [group α] (φ : α → Type v) (h : is_subgroup φ) :=
Π n g, φ n → φ (conjugate n g)

lemma mul_uniq {α : Type u} {a b c d : α} [magma α] (h : a = b) (g : c = d) :
  a · c = b · d :=
begin induction h, induction g, reflexivity end

theorem ker_is_subgroup {α : Type u} {β : Type v} [group α] [group β]
  (φ : homo α β) : is_subgroup (ker φ) :=
{ unit := begin
    unfold ker, apply square_is_unique,
    symmetry, transitivity, { apply eq.map, apply identity_sqr },
    apply φ.snd
  end,
  mul := begin
    intros a b h g,
    unfold ker at h, unfold ker at g, unfold ker,
    transitivity, apply φ.snd, symmetry,
    transitivity, apply identity_sqr,
    apply mul_uniq, exact h⁻¹, exact g⁻¹
  end,
  inv := begin
    intros x h,
    unfold ker at h, unfold ker,
    apply square_is_unique, symmetry, cases φ with φ H, calc
      φ x⁻¹ = φ (x⁻¹ · 1) : φ # (monoid.right_unit x⁻¹)⁻¹
        ... = φ (x⁻¹ · (x⁻¹ · x)) :
              begin
                apply eq.map (φ ∘ magma.mul x⁻¹), symmetry,
                apply group.left_inv
              end
        ... = φ x⁻¹ · φ (x⁻¹ · x) : by apply H
        ... = φ x⁻¹ · (φ x⁻¹ · φ x) : begin apply eq.map, apply H end
        ... = φ x⁻¹ · (φ x⁻¹ · 1) : begin repeat { apply eq.map }, exact h end
        ... = φ x⁻¹ · φ x⁻¹ : begin apply eq.map, apply monoid.right_unit end
  end }

theorem ker_is_normal_subgroup {α : Type u} {β : Type v} [group α] [group β]
  (φ : homo α β) : is_normal_subgroup (ker φ) (ker_is_subgroup φ) := begin
  intros n g h, cases φ with φ H,
  unfold ker at h, unfold ker, unfold conjugate, calc
    φ (g⁻¹ · n · g) = φ g⁻¹ · φ (n · g) : by apply H
                ... = φ g⁻¹ · φ n · φ g : begin apply eq.map, apply H end
                ... = φ g⁻¹ · 1 · φ g :
                      begin
                        apply eq.map (λ x, φ g⁻¹ · x · φ g),
                        exact h
                      end
                ... = φ g⁻¹ · φ g :
                      begin apply eq.map, apply monoid.left_unit end
                ... = φ (g⁻¹ · g) : begin symmetry, apply H end
                ... = φ 1 : φ # (group.left_inv g)
                ... = 1 : (ker_is_subgroup ⟨φ, H⟩).unit
end

def coeffspace (α : Type u) (β : Type v) :=
β → α → α

def is_eigenvalue {α : Type u} {β : Type v}
  (mul : coeffspace α β) (A : α → α) (x : α) :=
Σ y, A x = mul y x

def spectrum {α : Type u} {β : Type v}
  (mul : coeffspace α β) (A : α → α) :=
Σ x, is_eigenvalue mul A x

end ground_zero.algebra