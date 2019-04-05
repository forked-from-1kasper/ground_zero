import ground_zero.structures ground_zero.types.integer  ground_zero.types.swale
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
  begin symmetry, apply monoid.left_unit end
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

  def iso (α : Type u) (β : Type v) [group α] [group β] :=
  Σ (φ : α → β), is_homo φ × equiv.biinv φ

  infix ` ≅ `:25 := iso

  variable (φ : homo α β)
  def ker : swale α := λ g, φ.fst g = 1
  def Ker := Σ g, ker φ g

  def im : swale β := λ g, Σ f, φ.fst f = g
  def Im := Σ g, im φ g
end

structure is_subgroup {α : Type u} [group α] (φ : α → Type v) :=
(unit : φ 1)
(mul : Π a b, φ a → φ b → φ (a · b))
(inv : Π a, φ a → φ a⁻¹)

def is_normal_subgroup {α : Type u} [group α] (φ : α → Type v) (h : is_subgroup φ) :=
Π n g, φ n → φ (conjugate n g)

section
  variables {α : Type u} {φ : α → Type v} [group α]

  def left_coset (g : α) (h : is_subgroup φ) : swale α :=
  λ x, Σ h, g · h = x

  def right_coset (h : is_subgroup φ) (g : α) : swale α :=
  λ x, Σ h, h · g = x

  def factor_group (α : Type u) {φ : α → Type v} [group α]
    (h : is_subgroup φ) : swale (swale α) :=
  λ x, Σ g, left_coset g h = x
end

lemma mul_uniq {α : Type u} {a b c d : α} [magma α] (h : a = b) (g : c = d) :
  a · c = b · d :=
begin induction h, induction g, reflexivity end

theorem homo_saves_unit {α : Type u} {β : Type v} [group α] [group β]
  (φ : homo α β) : φ.fst 1 = 1 := begin
  cases φ with φ H, apply square_is_unique, calc
    φ 1 · φ 1 = φ (1 · 1) : (H 1 1)⁻¹
          ... = φ 1 : φ # identity_sqr⁻¹
end

theorem homo_respects_inv {α : Type u} {β : Type v} [group α] [group β]
  (φ : homo α β) (x : α) : φ.fst x⁻¹ = (φ.fst x)⁻¹ := begin
  cases φ with φ H, calc
    φ x⁻¹ = φ x⁻¹ · e : begin symmetry, apply monoid.right_unit end
      ... = φ x⁻¹ · (φ x · (φ x)⁻¹) :
            begin
              apply eq.map, symmetry,
              apply group.right_inv
            end
      ... = (φ x⁻¹ · φ x) · (φ x)⁻¹ : by apply monoid.assoc
      ... = φ (x⁻¹ · x) · (φ x)⁻¹ : (· (φ x)⁻¹) # (H x⁻¹ x)⁻¹
      ... = φ 1 · (φ x)⁻¹ :
            begin
              apply eq.map (λ y, φ y · (φ x)⁻¹),
              apply group.left_inv
            end
      ... = 1 · (φ x)⁻¹ : (· (φ x)⁻¹) # (homo_saves_unit ⟨φ, H⟩)
      ... = (φ x)⁻¹ : by apply monoid.left_unit
end

theorem ker_is_subgroup {α : Type u} {β : Type v} [group α] [group β]
  (φ : homo α β) : is_subgroup (ker φ) :=
{ unit := begin unfold ker, apply homo_saves_unit end,
  mul := begin
    intros a b h g,
    unfold ker at h, unfold ker at g, unfold ker,
    transitivity, apply φ.snd, symmetry,
    transitivity, apply identity_sqr,
    apply mul_uniq, exact h⁻¹, exact g⁻¹
  end,
  inv := begin
    intros x h,
    unfold ker at h, unfold ker, cases φ with φ H, calc
      φ x⁻¹ = (φ x)⁻¹ : homo_respects_inv ⟨φ, H⟩ x
        ... = 1⁻¹     : group.inv # h
        ... = 1       : identity_inv⁻¹
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

theorem im_is_subgroup {α : Type u} {β : Type v} [group α] [group β]
  (φ : homo α β) : is_subgroup (im φ) :=
{ unit := ⟨1, (ker_is_subgroup φ).unit⟩,
  mul := begin
    intros a b g h, unfold im at g, unfold im at h, unfold im,
    cases g with x g, cases h with y h,
    existsi (x · y), transitivity, apply φ.snd,
    induction g, induction h, reflexivity
  end,
  inv := begin
    intros x h, unfold im at h, unfold im,
    cases h with y h, existsi y⁻¹,
    transitivity, apply homo_respects_inv,
    apply eq.map, exact h
  end }

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

def coeffspace (α : Type u) (β : Type v) :=
β → α → α

def is_eigenvalue {α : Type u} {β : Type v}
  (mul : coeffspace α β) (A : α → α) (x : α) :=
Σ y, A x = mul y x

def spectrum {α : Type u} {β : Type v}
  (mul : coeffspace α β) (A : α → α) :=
Σ x, is_eigenvalue mul A x

end ground_zero.algebra