import ground_zero.algebra.core ground_zero.types.swale
open ground_zero ground_zero.types ground_zero.algebra.pointed_magma
open ground_zero.algebra (renaming group -> grp)

hott theory

namespace ground_zero.algebra.group

universes u v w
theorem group_unit_is_unique {α : Type u} [grp α] (e' : α)
  (right_unit' : Π x, x · e' = x)
  (left_unit' : Π x, e' · x = x)
  (H : 1 = e' → empty) : empty := begin
  have p := monoid.right_unit e',
  have q := left_unit' 1,
  exact H (q⁻¹ ⬝ p)
end

section
  variables {α : Type u} [grp α]

  def square_is_unique (x : α)
    (h : x · x = x) : x = 1 := calc
      x = 1 · x : begin symmetry, apply monoid.left_unit end
    ... = (x⁻¹ · x) · x :
          begin
            apply ground_zero.types.eq.map (· x),
            symmetry, apply algebra.group.left_inv x
          end
    ... = x⁻¹ · (x · x) : begin symmetry, apply monoid.assoc end
    ... = x⁻¹ · x : magma.mul x⁻¹ # h
    ... = 1 : by apply algebra.group.left_inv
  
  theorem inv_of_inv (x : α) : (x⁻¹)⁻¹ = x := calc
    (x⁻¹)⁻¹ = 1 · (x⁻¹)⁻¹ : begin symmetry, apply monoid.left_unit end
        ... = (x · x⁻¹) · (x⁻¹)⁻¹ :
              begin
                apply ground_zero.types.eq.map (· x⁻¹⁻¹),
                symmetry,
                apply algebra.group.right_inv x
              end
        ... = x · (x⁻¹ · x⁻¹⁻¹) : begin symmetry, apply monoid.assoc end
        ... = x · 1 : magma.mul x # (algebra.group.right_inv x⁻¹)
        ... = x : monoid.right_unit x

  theorem inv_inj (a b : α) (h : a⁻¹ = b⁻¹) : a = b :=
  (inv_of_inv a)⁻¹ ⬝ (inv # h) ⬝ (inv_of_inv b)
  
  theorem reduce_left (a b c : α)
    (h : c · a = c · b) : a = b := calc
      a = 1 · a         : (monoid.left_unit a)⁻¹
    ... = (c⁻¹ · c) · a : (· a) # (algebra.group.left_inv c)⁻¹
    ... = c⁻¹ · (c · a) : begin symmetry, apply monoid.assoc end
    ... = c⁻¹ · (c · b) : magma.mul c⁻¹ # h
    ... = (c⁻¹ · c) · b : by apply monoid.assoc
    ... = 1 · b         : (· b) # (algebra.group.left_inv c)
    ... = b             : monoid.left_unit b

  def identity_inv : 1 = 1⁻¹ :> α :=
  (algebra.group.right_inv 1)⁻¹ ⬝ monoid.left_unit 1⁻¹

  def identity_sqr : 1 = 1 · 1 :> α :=
  begin symmetry, apply monoid.left_unit end

  theorem inv_uniq {a b : α} (h : a · b = 1) : a⁻¹ = b := calc
    a⁻¹ = a⁻¹ · 1 : (monoid.right_unit a⁻¹)⁻¹
    ... = a⁻¹ · (a · b) : magma.mul a⁻¹ # h⁻¹
    ... = (a⁻¹ · a) · b : by apply monoid.assoc
    ... = 1 · b : (· b) # (algebra.group.left_inv a)
    ... = b : by apply monoid.left_unit

  theorem inv_explode (x y : α) : (x · y)⁻¹ = y⁻¹ · x⁻¹ := begin
    apply inv_uniq, calc
      (x · y) · y⁻¹ · x⁻¹ = ((x · y) · y⁻¹) · x⁻¹ : by apply monoid.assoc
                      ... = (x · 1) · x⁻¹ :
                            begin
                              apply eq.map (· x⁻¹), transitivity,
                              { symmetry, apply monoid.assoc },
                              { apply eq.map, apply group.right_inv }
                            end
                      ... = x · x⁻¹ : (· x⁻¹) # (monoid.right_unit x)
                      ... = 1 : by apply group.right_inv
  end
end

def commutes {α : Type u} [grp α] (x y : α) :=
x · y = y · x

def Zentrum (α : Type u) [grp α] :=
Σ (z : α), Π g, commutes z g

def commutator {α : Type u} [grp α] (g h : α) :=
g⁻¹ · h⁻¹ · g · h

def conjugate {α : Type u} [grp α] (a x : α) :=
x⁻¹ · a · x

instance {α : Type u} [grp α] : has_pow α α := ⟨conjugate⟩

theorem conjugate_distrib {α : Type u} [grp α]
  (g x y : α) : g ^ (x · y) = (g ^ x) ^ y := calc
    g ^ (x · y) = (x · y)⁻¹ · g · (x · y) : by reflexivity
            ... = (y⁻¹ · x⁻¹) · g · (x · y) :
                    (· g · (x · y)) # (inv_explode x y)
            ... = y⁻¹ · x⁻¹ · g · (x · y) :
                  begin symmetry, apply monoid.assoc end
            ... = y⁻¹ · x⁻¹ · ((g · x) · y) :
                  begin
                    apply eq.map (λ h, y⁻¹ · x⁻¹ · h),
                    apply monoid.assoc
                  end
            ... = y⁻¹ · (x⁻¹ · g · x) · y :
                  begin apply eq.map, apply monoid.assoc end
            ... = (g ^ x) ^ y : by reflexivity

theorem conjugate_id {α : Type u} [grp α] (g : α) : g ^ (e : α) = g := calc
   g ^ (e : α) = e⁻¹ · g · e : by reflexivity
           ... = e⁻¹ · g : (magma.mul e⁻¹) # (monoid.right_unit g)
           ... = e · g : (· g) # identity_inv⁻¹
           ... = g : by apply monoid.left_unit

section
  variables {α : Type u} {β : Type v} [grp α] [grp β]

  def is_homo (φ : α → β) :=
  Π a b, φ (a · b) = φ a · φ b

  def homo (α : Type u) (β : Type v) [grp α] [grp β] :=
  Σ (φ : α → β), is_homo φ

  infix ` ⤳ `:20 := homo

  def homo.comp {α : Type u} {β : Type v} {φ : Type w} [grp α] [grp β] [grp φ]
    (f : β ⤳ φ) (g : α ⤳ β) : α ⤳ φ :=
  ⟨f.fst ∘ g.fst, begin
    intros a b, cases f with f F, cases g with g G, calc
      (f ∘ g) (a · b) = f (g a · g b) : f # (G a b)
                  ... = (f ∘ g) a · (f ∘ g) b : by apply F
  end⟩

  infix ` ⋅ `:60 := homo.comp

  def zero : α ⤳ β :=
  ⟨λ _, 1, λ _ _, (monoid.left_unit (e : β))⁻¹⟩

  instance : has_zero (α ⤳ β) := ⟨zero⟩

  def iso (α : Type u) (β : Type v) [grp α] [grp β] :=
  Σ (φ : α → β), is_homo φ × equiv.biinv φ

  infix ` ≅ `:25 := iso

  variable (φ : α ⤳ β)
  def ker : swale α := λ g, φ.fst g = 1
  def Ker := swale.subtype (ker φ)

  def im : swale β := λ g, Σ f, φ.fst f = g
  def Im := swale.subtype (im φ)
end

class is_subgroup {α : Type u} [grp α] (φ : α → Type v) :=
(unit : φ 1)
(mul : Π a b, φ a → φ b → φ (a · b))
(inv : Π a, φ a → φ a⁻¹)

def subgroup.mul {α : Type u} [grp α] (φ : α → Type v)
  [is_subgroup φ] (x y : swale.subtype φ) : swale.subtype φ := begin
  cases x with x h, cases y with y g, existsi (x · y),
  apply is_subgroup.mul; assumption
end

def subgroup.inv {α : Type u} [grp α] (φ : α → Type v)
  [is_subgroup φ] (x : swale.subtype φ) : swale.subtype φ := begin
  cases x with x h, existsi x⁻¹,
  apply is_subgroup.inv; assumption
end

instance subgroup.magma {α : Type u} [grp α] (φ : α → Type v)
  [is_subgroup φ] : magma (swale.subtype φ) :=
⟨subgroup.mul φ⟩

instance subgroup.pointed_magma {α : Type u} [grp α] (φ : α → Type v)
  [is_subgroup φ] : pointed_magma (swale.subtype φ) :=
⟨⟨1, is_subgroup.unit φ⟩⟩

class is_normal_subgroup {α : Type u} [grp α] (φ : α → Type v) extends is_subgroup φ :=
(conj : Π (n g : α), φ n → φ (n ^ g))

section
  variables {α : Type u} [grp α]

  def left_coset (g : α) (φ : α → Type v) [is_subgroup φ] : swale α :=
  λ x, Σ h, g · h = x

  def right_coset (φ : α → Type v) (g : α) [is_subgroup φ] : swale α :=
  λ x, Σ h, h · g = x

  def factor_group (α : Type u) (φ : α → Type v)
    [grp α] [is_normal_subgroup φ] : swale (swale α) :=
  λ x, Σ g, left_coset g φ = x

  def factor (α : Type u) (φ : α → Type v)
    [grp α] [is_normal_subgroup φ] :=
  swale.subtype (factor_group α φ)

  infix `/` := factor

  def factor.mul {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] (x y : α/φ) : α/φ := begin
    cases x with x h, cases h with a h,
    cases y with y g, cases g with b g,
    existsi left_coset (a · b) φ,
    existsi (a · b), trivial
  end

  instance factor.has_binop {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] : magma (α/φ) :=
  ⟨factor.mul⟩

  instance factor.has_unit {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] : pointed_magma (α/φ) :=
  ⟨⟨left_coset 1 φ, ⟨1, by trivial⟩⟩⟩

  def factor.incl {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] (x : α) : α/φ :=
  ⟨left_coset x φ, ⟨x, types.eq.refl (left_coset x φ)⟩⟩

  def factor.left_unit {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] (x : α/φ) : x · 1 = x := begin
    cases x with x h, cases h with a h, induction h,
    apply eq.map factor.incl, apply monoid.right_unit
  end

  def factor.right_unit {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] (x : α/φ) : 1 · x = x := begin
    cases x with x h, cases h with a h, induction h,
    apply eq.map factor.incl, apply monoid.left_unit
  end

  def factor.assoc {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] (x y z : α/φ) :
    x · (y · z) = (x · y) · z := begin
    cases x with x h, cases h with a h,
    cases y with y g, cases g with b g,
    cases z with z f, cases f with c f,
    induction h, induction g, induction f,
    apply eq.map factor.incl, apply monoid.assoc
  end

  instance factor.is_monoid {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] : algebra.monoid (α/φ) :=
  ⟨factor.left_unit, factor.right_unit, factor.assoc⟩

  def factor.inv {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] (x : α/φ) : α/φ := begin
    cases x with x h, cases h with a h, apply factor.incl a⁻¹
  end

  def factor.right_inv {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] (x : α/φ) :
    x · factor.inv x = 1 := begin
    cases x with x h, cases h with a h,
    induction h, apply eq.map factor.incl,
    apply group.right_inv
  end

  def factor.left_inv {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] (x : α/φ) :
    factor.inv x · x = 1 := begin
    cases x with x h, cases h with a h,
    induction h, apply eq.map factor.incl,
    apply group.left_inv
  end

  instance factor.is_group {α : Type u} {φ : α → Type v}
    [grp α] [is_normal_subgroup φ] : grp (α/φ) :=
  ⟨factor.inv, factor.right_inv, factor.left_inv⟩
end

def mul_uniq {α : Type u} {a b c d : α} [magma α] (h : a = b) (g : c = d) :
  a · c = b · d :=
begin induction h, induction g, reflexivity end

def homo_saves_unit {α : Type u} {β : Type v} [grp α] [grp β]
  (φ : α ⤳ β) : φ.fst 1 = 1 := begin
  cases φ with φ H, apply square_is_unique, calc
    φ 1 · φ 1 = φ (1 · 1) : (H 1 1)⁻¹
          ... = φ 1 : φ # identity_sqr⁻¹
end

def homo_respects_inv {α : Type u} {β : Type v} [grp α] [grp β]
  (φ : α ⤳ β) (x : α) : φ.fst x⁻¹ = (φ.fst x)⁻¹ := begin
  cases φ with φ H, calc
    φ x⁻¹ = φ x⁻¹ · 1 : begin symmetry, apply monoid.right_unit end
      ... = φ x⁻¹ · (φ x · (φ x)⁻¹) :
            begin
              apply eq.map, symmetry,
              apply algebra.group.right_inv
            end
      ... = (φ x⁻¹ · φ x) · (φ x)⁻¹ : by apply monoid.assoc
      ... = φ (x⁻¹ · x) · (φ x)⁻¹ : (· (φ x)⁻¹) # (H x⁻¹ x)⁻¹
      ... = φ 1 · (φ x)⁻¹ :
            begin
              apply eq.map (λ y, φ y · (φ x)⁻¹),
              apply algebra.group.left_inv
            end
      ... = 1 · (φ x)⁻¹ : (· (φ x)⁻¹) # (homo_saves_unit ⟨φ, H⟩)
      ... = (φ x)⁻¹ : by apply monoid.left_unit
end

def right_div {α : Type u} [grp α] (x y : α) := x · y⁻¹
def left_div {α : Type u} [grp α] (x y : α) := x⁻¹ · y

instance {α : Type u} [grp α] : has_div α := ⟨right_div⟩
instance {α : Type u} [grp α] : has_sdiff α := ⟨left_div⟩

lemma homo_respects_div {α : Type u} {β : Type v} [grp α] [grp β]
  (φ : α ⤳ β) (x y : α) : φ.fst (x / y) = φ.fst x / φ.fst y := begin
  cases φ with φ H, calc
    φ (x / y) = φ x · φ y⁻¹ : by apply H
          ... = φ x · (φ y)⁻¹ :
                begin apply eq.map, apply homo_respects_inv ⟨φ, H⟩ end
          ... = φ x / φ y : by reflexivity
end

instance ker_is_subgroup {α : Type u} {β : Type v} [grp α] [grp β]
  (φ : α ⤳ β) : is_subgroup (ker φ) :=
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
        ... = 1⁻¹     : algebra.group.inv # h
        ... = 1       : identity_inv⁻¹
  end }

instance ker_is_normal_subgroup {α : Type u} {β : Type v} [grp α] [grp β]
  (φ : α ⤳ β) : is_normal_subgroup (ker φ) := begin
  apply is_normal_subgroup.mk, intros n g h, cases φ with φ H,
  unfold ker at h, unfold ker, unfold has_pow.pow, unfold conjugate, calc
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
                ... = φ 1 : φ # (algebra.group.left_inv g)
                ... = 1 : homo_saves_unit ⟨φ, H⟩
end

instance im_is_subgroup {α : Type u} {β : Type v} [grp α] [grp β]
  (φ : α ⤳ β) : is_subgroup (im φ) :=
{ unit := ⟨1, homo_saves_unit φ⟩,
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

def tower {α : Type u} [grp α] (a : α) :=
Σ (b : α) (n : integer), b = a^n

def cyclic {α : Type u} [grp α] (a : α) :=
grp (tower a)

class vector (α : Type u) (β : Type v) [pointed_magma β] extends algebra.group α :=
(comm : Π (x y : α), x · y = y · x)
(ap : β → α → α) (unit : Π x, ap 1 x = x)
(ap_assoc : Π a b x, ap a (ap b x) = ap (a · b) x)
(distrib_scalar : Π a b x, ap (a · b) x = ap a x · ap b x)
(distrib_vector : Π a x y, ap a (x · y) = ap a x · ap a y)

def is_eigenvalue {α : Type u} {β : Type v} [pointed_magma β] [vector α β] (A : α → α) (x : α) :=
Σ (y : β), A x = vector.ap y x

end ground_zero.algebra.group