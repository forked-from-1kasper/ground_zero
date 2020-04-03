import ground_zero.theorems.functions ground_zero.theorems.ua
import ground_zero.HITs.quotient
open ground_zero.types.equiv (biinv transport)
open ground_zero.types.eq (map)
open ground_zero.structures

namespace ground_zero.algebra
universes u v w

hott theory

def set (α : Type u) := Σ (φ : α → Type v), Π x, prop (φ x)
def set.contains {α : Type u} (x : α) (s : set α) : Type v := s.fst x
infix ∈ := set.contains

def set.prop {α : Type u} (x : α) (s : set α) : prop (x ∈ s) := s.snd x
def set.subtype {α : Type u} (s : set α) := Σ x, s.fst x

@[hott] def set.hset {α : Type u} (s : set α) : hset α → hset s.subtype := begin
  intro H, apply zero_eqv_set.forward,
  fapply ground_zero.structures.ntype_respects_sigma 0,
  { apply zero_eqv_set.left, intros a b, apply H },
  { intro x, apply zero_eqv_set.left,
    apply prop_is_set, apply s.snd }
end

class magma (α : Type u) extends has_mul α :=
(set : hset α)

class semigroup (α : Type u) extends magma α :=
(mul_assoc : Π (a b c : α), (a * b) * c = a * (b * c))

class monoid (α : Type u) extends semigroup α, has_one α :=
(one_mul : Π (a : α), 1 * a = a) (mul_one : Π (a : α), a * 1 = a)

class group (α : Type u) extends monoid α, has_inv α :=
(mul_left_inv : Π (a : α), a⁻¹ * a = 1)

class abelian (α : Type u) extends group α :=
(mul_comm : Π (a b : α), a * b = b * a)

@[hott] def mul_uniq {α : Type u} {a b c d : α} [has_mul α]
  (h : a = b) (g : c = d) : a * c = b * d :=
begin induction h, induction g, reflexivity end

namespace group
  variables {α : Type u} [group α]

  @[hott] def left_unit_uniq (e : α) (one_mul' : Π a, e * a = a) : e = 1 :=
  (monoid.mul_one e)⁻¹ ⬝ one_mul' 1

  @[hott] def right_unit_uniq (e : α) (mul_one' : Π a, a * e = a) : e = 1 :=
  (monoid.one_mul e)⁻¹ ⬝ mul_one' 1

  @[hott] def unit_of_sqr {x : α} (h : x * x = x) := calc
      x = 1 * x         : by symmetry; apply monoid.one_mul
    ... = (x⁻¹ * x) * x : (* x) # (group.mul_left_inv x)⁻¹
    ... = x⁻¹ * (x * x) : by apply semigroup.mul_assoc
    ... = x⁻¹ * x       : has_mul.mul x⁻¹ # h
    ... = 1             : by apply group.mul_left_inv

  @[hott] def inv_eq_of_mul_eq_one {x y : α} (h : x * y = 1) := calc
     x⁻¹ = x⁻¹ * 1       : by symmetry; apply monoid.mul_one
     ... = x⁻¹ * (x * y) : has_mul.mul x⁻¹ # h⁻¹
     ... = (x⁻¹ * x) * y : by symmetry; apply semigroup.mul_assoc
     ... = 1 * y         : (* y) # (group.mul_left_inv x)
     ... = y             : by apply monoid.one_mul

  @[hott] def inv_inv (x : α) : x⁻¹⁻¹ = x :=
  inv_eq_of_mul_eq_one (group.mul_left_inv x)

  @[hott] def eq_inv_of_mul_eq_one {x y : α} (h : x * y = 1) : x = y⁻¹ :=
  (inv_inv x)⁻¹ ⬝ has_inv.inv # (inv_eq_of_mul_eq_one h)

  @[hott] def mul_right_inv (x : α) := calc
    x * x⁻¹ = x⁻¹⁻¹ * x⁻¹ : (* x⁻¹) # (inv_inv x)⁻¹
        ... = 1           : by apply group.mul_left_inv x⁻¹

  @[hott] def inv_inj {x y : α} (h : x⁻¹ = y⁻¹) : x = y := calc
      x = x⁻¹⁻¹ : (inv_inv x)⁻¹
    ... = y⁻¹⁻¹ : has_inv.inv # h
    ... = y     : inv_inv y

  @[hott] def mul_cancel_left {a b c : α} (h : c * a = c * b) := calc
      a = 1 * a         : (monoid.one_mul a)⁻¹
    ... = (c⁻¹ * c) * a : (* a) # (group.mul_left_inv c)⁻¹
    ... = c⁻¹ * (c * a) : by apply semigroup.mul_assoc
    ... = c⁻¹ * (c * b) : has_mul.mul c⁻¹ # h
    ... = (c⁻¹ * c) * b : by symmetry; apply semigroup.mul_assoc
    ... = 1 * b         : (* b) # (group.mul_left_inv c)
    ... = b             : monoid.one_mul b

  @[hott] def unit_inv : (1 : α) = 1⁻¹ :=
  (mul_right_inv 1)⁻¹ ⬝ monoid.one_mul 1⁻¹

  @[hott] def unit_sqr : (1 : α) = 1 * 1 :=
  begin symmetry, apply monoid.one_mul end

  @[hott] def inv_explode (x y : α) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
  inv_eq_of_mul_eq_one
    (calc (x * y) * (y⁻¹ * x⁻¹)
        = ((x * y) * y⁻¹) * x⁻¹ :
          by symmetry; apply semigroup.mul_assoc
    ... = (x * 1) * x⁻¹ :
          begin
            apply map (* x⁻¹), transitivity,
            { apply semigroup.mul_assoc },
            { apply map, apply mul_right_inv }
          end
    ... = x * x⁻¹ : (* x⁻¹) # (monoid.mul_one x)
    ... = 1 : by apply mul_right_inv)

  def conjugate (a x : α) := x⁻¹ * a * x
  instance : has_pow α α := ⟨conjugate⟩
  def conjugate_rev (a x : α) := x * a * x⁻¹

  def right_div (x y : α) := x * y⁻¹
  def left_div  (x y : α) := x⁻¹ * y

  instance : has_div α   := ⟨right_div⟩
  instance : has_sdiff α := ⟨left_div⟩

  section
    variables {β : Type v} [group β]

    def respects_mul (φ : α → β) :=
    Π a b, φ (a * b) = φ a * φ b

    @[hott] def homo (α : Type u) (β : Type v) [group α] [group β] :=
    Σ (φ : α → β), respects_mul φ

    infix ` ⤳ `:20 := homo

    @[hott] def prop_respects_mul (φ : α → β) : prop (respects_mul φ) := begin
      intros f g,
      repeat { apply ground_zero.theorems.funext, intro },
      apply magma.set
    end

    @[hott] def homo.comp {α : Type u} {β : Type v} {φ : Type w}
      [group α] [group β]   [group φ]
      (f : β ⤳ φ) (g : α ⤳ β) : α ⤳ φ := begin
      cases f with f F, cases g with g G,
      existsi f ∘ g, intros a b, calc
        (f ∘ g) (a * b) = f (g a * g b)         : f # (G a b)
                    ... = (f ∘ g) a * (f ∘ g) b : by apply F
    end

    infix ` ⋅ `:60 := homo.comp

    @[hott] def homo.zero : α ⤳ β :=
    ⟨λ _, 1, λ _ _, (monoid.one_mul 1)⁻¹⟩
    instance : has_zero (α ⤳ β) := ⟨homo.zero⟩

    variable (φ : α ⤳ β)
    def ker.aux := λ g, φ.fst g = 1
    @[hott] def ker_is_prop (x : α) : prop (ker.aux φ x) :=
    begin intros f g, apply magma.set end

    def ker : set α := ⟨ker.aux φ, ker_is_prop φ⟩
    def Ker := (ker φ).subtype

    def im.aux := ground_zero.theorems.functions.fib_inh (φ.fst)
    def im : set β := ⟨im.aux φ, λ _, ground_zero.HITs.merely.uniq⟩
    def Im := (im φ).subtype
  end

  @[hott] def iso (α : Type u) (β : Type v) [group α] [group β] :=
  Σ (f : α → β), respects_mul f × biinv f
  infix ` ≅ `:25 := iso

  @[refl] def iso.refl (α : Type u) [group α] : α ≅ α := begin
    existsi id, split,
    { intros a b, trivial },
    { split; existsi id; intro x; reflexivity }
  end

  class is_subgroup (φ : set α) :=
  (unit : (1 : α) ∈ φ)
  (mul : Π a b, a ∈ φ → b ∈ φ → a * b ∈ φ)
  (inv : Π a, a ∈ φ → a⁻¹ ∈ φ)

  class is_normal_subgroup (φ : set α)
    extends is_subgroup φ :=
  (cosets_eqv : Π {g h : α}, g * h ∈ φ → h * g ∈ φ)

  @[hott] def cancel_left (a b : α) := calc
      a = a * 1         : (monoid.mul_one a)⁻¹
    ... = a * (b⁻¹ * b) : (has_mul.mul a) # (mul_left_inv b)⁻¹
    ... = (a * b⁻¹) * b : (semigroup.mul_assoc a b⁻¹ b)⁻¹

  @[hott] def cancel_right (a b : α) := calc
      a = a * 1         : (monoid.mul_one a)⁻¹
    ... = a * (b * b⁻¹) : (has_mul.mul a) # (mul_right_inv b)⁻¹
    ... = (a * b) * b⁻¹ : (semigroup.mul_assoc a b b⁻¹)⁻¹

  @[hott] def is_normal_subgroup.conj (φ : set α)
    [is_normal_subgroup φ] (n g : α) : n ∈ φ → n ^ g ∈ φ := begin
    intro h, change g⁻¹ * n * g ∈ φ,
    apply ground_zero.types.equiv.transport (∈ φ),
    { symmetry, apply semigroup.mul_assoc },
    apply is_normal_subgroup.cosets_eqv,
    apply ground_zero.types.equiv.transport (∈ φ),
    apply cancel_right, assumption
  end

  @[hott] def conjugate_eqv (φ : set α)
    [is_normal_subgroup φ] (n g : α) :
    conjugate n g ∈ φ → conjugate_rev n g ∈ φ := begin
    intro h, apply is_normal_subgroup.cosets_eqv,
    apply transport (∈ φ),
    calc g * (g⁻¹ * n) = (g * g⁻¹) * n : (semigroup.mul_assoc g g⁻¹ n)⁻¹
                   ... = 1 * n         : (* n) # (group.mul_right_inv g)
                   ... = (g⁻¹ * g) * n : (* n) # (group.mul_left_inv g)⁻¹
                   ... = g⁻¹ * (g * n) : semigroup.mul_assoc g⁻¹ g n,
    apply is_normal_subgroup.cosets_eqv, assumption
  end

  def ldiv (φ : set α) [is_subgroup φ] := λ x y, x \ y ∈ φ
  def rdiv (φ : set α) [is_subgroup φ] := λ x y, x / y ∈ φ

  @[hott] def inv_x_mul_y_inv (x y : α) := calc
    (x⁻¹ * y)⁻¹ = y⁻¹ * x⁻¹⁻¹ : by apply inv_explode
            ... = y⁻¹ * x     : (has_mul.mul y⁻¹) # (inv_inv x)

  @[hott] def x_mul_inv_y_inv (x y : α) :=  calc
    (x * y⁻¹)⁻¹ = y⁻¹⁻¹ * x⁻¹ : by apply inv_explode
            ... = y * x⁻¹     : (* x⁻¹) # (inv_inv y)

  @[hott] def normal_subgroup_cosets (φ : set α) [is_normal_subgroup φ] :
    Π {x y}, ldiv φ x y ↔ rdiv φ x y := begin
    intros x y, split; intro h,
    { change x * y⁻¹ ∈ φ, apply transport (∈ φ),
      calc x * (y⁻¹ * x) * x⁻¹ = x * (y⁻¹ * x * x⁻¹) :
                                 semigroup.mul_assoc x (y \ x) x⁻¹
                           ... = x * y⁻¹ :
                                 (has_mul.mul x) # (cancel_right y⁻¹ x)⁻¹,
      apply conjugate_eqv,
      apply is_normal_subgroup.conj,
      apply transport (∈ φ), apply inv_x_mul_y_inv,
      apply is_subgroup.inv, assumption },
    { change x⁻¹ * y ∈ φ, apply transport (∈ φ),
      calc x⁻¹ * (y * x⁻¹) * x = x⁻¹ * (y * x⁻¹ * x) :
                                 semigroup.mul_assoc x⁻¹ (y / x) x
                           ... = x⁻¹ * y :
                                 (has_mul.mul x⁻¹) # (cancel_left y x)⁻¹,
      apply is_normal_subgroup.conj, apply transport (∈ φ),
      apply x_mul_inv_y_inv,
      apply is_subgroup.inv, assumption }
  end

  @[hott] noncomputable def cosets_eq (φ : set α)
    [is_normal_subgroup φ] : ldiv φ = rdiv φ := begin
    repeat { apply ground_zero.theorems.funext, intro },
    apply ground_zero.ua.propext,
    repeat { apply set.prop },
    apply normal_subgroup_cosets
  end

  @[hott] def chain_ldiv (x y z : α) := calc
    (x \ y) * (y \ z) = (x⁻¹ * y) * (y⁻¹ * z) : by refl
                  ... = x⁻¹ * (y * (y⁻¹ * z)) : (semigroup.mul_assoc x⁻¹ y (y⁻¹ * z))
                  ... = x⁻¹ * ((y * y⁻¹) * z) : (has_mul.mul x⁻¹) # (semigroup.mul_assoc y y⁻¹ z)⁻¹
                  ... = x⁻¹ * (1 * z)         :
                        begin apply map, apply map (* z),
                              apply group.mul_right_inv end
                  ... = x \ z : (λ y, x⁻¹ * y) # (monoid.one_mul z)

  @[hott] def chain_rdiv (x y z : α) := calc
    (x / y) * (y / z) = (x * y⁻¹) * (y * z⁻¹) : by refl
                  ... = x * (y⁻¹ * (y * z⁻¹)) : (semigroup.mul_assoc x y⁻¹ (y * z⁻¹))
                  ... = x * ((y⁻¹ * y) * z⁻¹) : (has_mul.mul x) # (semigroup.mul_assoc y⁻¹ y z⁻¹)⁻¹
                  ... = x * (1 * z⁻¹)         :
                        begin apply map, apply map (* z⁻¹),
                              apply group.mul_left_inv end
                  ... = x / z : (λ y, x * y) # (monoid.one_mul z⁻¹)

  @[hott] def factor_left_rel (φ : set α) [is_subgroup φ] : α → α → Ω :=
  λ x y, ⟨ldiv φ x y, by apply set.prop⟩

  @[hott] def factor_right_rel (φ : set α) [is_subgroup φ] : α → α → Ω :=
  λ x y, ⟨rdiv φ x y, by apply set.prop⟩

  @[hott] def factor_setoid_left (φ : set α)
    [is_subgroup φ] : ground_zero.HITs.setoid α :=
  ⟨factor_left_rel φ, begin
    split,
    { intro x, apply transport (∈ φ),
      symmetry, apply group.mul_left_inv,
      apply is_subgroup.unit },
    split,
    { intros x y h, apply transport (∈ φ), apply inv_x_mul_y_inv,
      apply is_subgroup.inv, assumption },
    { intros x y z h g, apply transport (∈ φ),
      apply chain_ldiv x y z, apply is_subgroup.mul;
      assumption }
  end⟩

  @[hott] def factor_setoid_right (φ : set α)
    [is_subgroup φ] : ground_zero.HITs.setoid α :=
  ⟨factor_right_rel φ, begin
    split,
    { intro x, apply transport (∈ φ),
      symmetry, apply group.mul_right_inv,
      apply is_subgroup.unit },
    split,
    { intros x y h, apply transport (∈ φ), apply x_mul_inv_y_inv,
      apply is_subgroup.inv, assumption },
    { intros x y z h g, apply transport (∈ φ),
      apply chain_rdiv x y z, apply is_subgroup.mul;
      assumption }
  end⟩

  def factor (α : Type u) [group α] (φ : set α) [is_subgroup φ] :=
  ground_zero.HITs.quotient (factor_setoid_left φ)
  infix `/` := factor

  def factor_right (α : Type u) [group α] (φ : set α) [is_subgroup φ] :=
  ground_zero.HITs.quotient (factor_setoid_right φ)
  infix `\` := factor_right

  @[hott] noncomputable def factor_symm (φ : set α)
    [is_normal_subgroup φ] : α/φ = α\φ := begin
      apply map ground_zero.HITs.quotient, apply ground_zero.HITs.setoid.eq,
      repeat { apply ground_zero.theorems.funext, intro },
      fapply ground_zero.types.sigma.prod,
      { change ldiv φ _ _ = rdiv φ _ _,
        repeat { apply ground_zero.HITs.interval.happly },
        apply cosets_eq },
      apply prop_is_prop
    end

  def factor.incl {φ : set α} [is_normal_subgroup φ] : α → α/φ :=
  ground_zero.HITs.quotient.elem

  section
    variables {φ : set α} [is_normal_subgroup φ]

    @[hott] noncomputable def factor.mul : α/φ → α/φ → α/φ := begin
      fapply ground_zero.HITs.quotient.lift₂,
      { intros a b, exact factor.incl (a * b) },
      { apply ground_zero.HITs.quotient.set },
      { intros a b c d H G,
        apply ground_zero.HITs.quotient.sound,
        change _ ∈ φ, apply transport (∈ φ),
        calc b⁻¹ * (a⁻¹ * c * (d * b⁻¹)) * b
           = b⁻¹ * (a⁻¹ * c * d * b⁻¹) * b :
             (λ x, b⁻¹ * x * b) # (semigroup.mul_assoc (a⁻¹ * c) d b⁻¹)⁻¹
       ... = b⁻¹ * (a⁻¹ * c * d * b⁻¹ * b) :
             semigroup.mul_assoc b⁻¹ (a⁻¹ * c * d * b⁻¹) b
       ... = b⁻¹ * (a⁻¹ * c * d * (b⁻¹ * b)) :
             (λ x, b⁻¹ * x) # (semigroup.mul_assoc (a⁻¹ * c * d) b⁻¹ b)
       ... = b⁻¹ * (a⁻¹ * c * d * 1) :
             @map α α _ _ (λ x, b⁻¹ * (a⁻¹ * c * d * x)) (group.mul_left_inv b)
       ... = b⁻¹ * (a⁻¹ * c * d) :
             (λ x, b⁻¹ * x) # (monoid.mul_one (a⁻¹ * c * d))
       ... = b⁻¹ * (a⁻¹ * (c * d)) :
             (λ x, b⁻¹ * x) # (semigroup.mul_assoc a⁻¹ c d)
       ... = (b⁻¹ * a⁻¹) * (c * d) :
             (semigroup.mul_assoc b⁻¹ a⁻¹ (c * d))⁻¹
       ... = (a * b) \ (c * d) :
             (* (c * d)) # (inv_explode a b)⁻¹,
        apply is_normal_subgroup.conj,
        apply is_subgroup.mul,
        { exact H },
        { apply transport (∈ φ), calc
            (b * d⁻¹)⁻¹ = d⁻¹⁻¹ * b⁻¹ : inv_explode b d⁻¹
                    ... = d * b⁻¹ : (* b⁻¹) # (inv_inv d),
          apply is_subgroup.inv,
          apply (normal_subgroup_cosets φ).left,
          exact G } }
    end

    noncomputable instance : has_mul (α/φ) :=
    ⟨factor.mul⟩

    @[hott] def factor.one : α/φ := factor.incl 1
    instance : has_one (α/φ) := ⟨factor.one⟩

    @[hott] noncomputable def factor.mul_one (x : α/φ) : x * 1 = x := begin
      fapply ground_zero.HITs.quotient.ind_prop _ _ x; clear x,
      { intro x, apply ground_zero.HITs.quotient.sound,
        apply transport (∈ φ), calc
            1 = x⁻¹ * x             : (group.mul_left_inv x)⁻¹
          ... = 1 * x⁻¹ * x         : (* x) # (monoid.one_mul x⁻¹)⁻¹
          ... = (1 : α)⁻¹ * x⁻¹ * x : (λ y, y * x⁻¹ * x) # unit_inv
          ... = (x * 1)⁻¹ * x       : (* x) # (inv_explode x 1)⁻¹,
        apply is_subgroup.unit },
      { intros, apply ground_zero.HITs.quotient.set }
    end

    @[hott] noncomputable def factor.one_mul (x : α/φ) : 1 * x = x := begin
      fapply ground_zero.HITs.quotient.ind_prop _ _ x; clear x,
      { intro x, apply ground_zero.HITs.quotient.sound,
        apply transport (∈ φ), calc
            1 = x⁻¹ * x             : (group.mul_left_inv x)⁻¹
          ... = x⁻¹ * 1 * x         : (* x) # (monoid.mul_one x⁻¹)⁻¹
          ... = x⁻¹ * 1⁻¹ * x       : (λ y, x⁻¹ * y * x) # unit_inv
          ... = (1 * x)⁻¹ * x       : (* x) # (inv_explode 1 x)⁻¹,
        apply is_subgroup.unit },
      { intros, apply ground_zero.HITs.quotient.set }
    end

    @[hott] noncomputable def factor.assoc (x y z : α/φ) : x * y * z = x * (y * z) := begin
      fapply ground_zero.HITs.quotient.ind_prop _ _ x; clear x,
      { fapply ground_zero.HITs.quotient.ind_prop _ _ y; clear y,
        { fapply ground_zero.HITs.quotient.ind_prop _ _ z; clear z,
          { intros z y x, apply ground_zero.HITs.quotient.sound,
            apply transport (∈ φ), calc
                1 = (x * (y * z))⁻¹ * (x * (y * z)) :
                    (group.mul_left_inv (x * (y * z)))⁻¹
              ... = (x * y * z)⁻¹ * (x * (y * z)) :
                    (λ p, has_inv.inv p * (x * (y * z))) #
                      (semigroup.mul_assoc x y z)⁻¹,
            apply is_subgroup.unit },
          { repeat { intros, apply ground_zero.structures.pi_prop },
            intros, apply ground_zero.HITs.quotient.set } },
        { intros, apply ground_zero.structures.pi_prop,
          intros, apply ground_zero.HITs.quotient.set } },
      { intros, apply ground_zero.HITs.quotient.set }
    end

    @[hott] noncomputable def factor.inv (x : α/φ) : α/φ := begin
      apply ground_zero.HITs.quotient.rec _ _ _ x; clear x,
      { intro x, exact factor.incl x⁻¹ },
      { intros u v H, apply ground_zero.HITs.quotient.sound,
        apply transport (∈ φ), { symmetry, apply map (* v⁻¹), apply inv_inv },
        apply (normal_subgroup_cosets φ).left, exact H },
      { apply ground_zero.HITs.quotient.set }
    end
    noncomputable instance : has_inv (α/φ) := ⟨factor.inv⟩

    @[hott] noncomputable def factor.left_inv (x : α/φ) : x⁻¹ * x = 1 := begin
      fapply ground_zero.HITs.quotient.ind_prop _ _ x; clear x,
      { intro x, apply ground_zero.HITs.quotient.sound,
        apply transport (∈ φ), calc
            1 = x⁻¹ * x⁻¹⁻¹     : (group.mul_right_inv x⁻¹)⁻¹
          ... = x⁻¹ * x⁻¹⁻¹ * 1 : (monoid.mul_one _)⁻¹
          ... = x⁻¹ * x \ 1     : @map α α _ _ (* 1) (inv_explode x⁻¹ x)⁻¹,
        apply is_subgroup.unit },
      { intros, apply ground_zero.HITs.quotient.set }
    end

    @[hott] noncomputable instance factor.is_group : group (α/φ) :=
    { set := λ _ _, ground_zero.HITs.quotient.set,
      mul := factor.mul,
      one := factor.one,
      mul_assoc := factor.assoc,
      one_mul := factor.one_mul,
      mul_one := factor.mul_one,
      inv := factor.inv,
      mul_left_inv := factor.left_inv }
  end

  section
    variables {β : Type v} [group β] (φ : α ⤳ β)
    @[hott] def homo_saves_unit : φ.fst 1 = 1 := begin
      cases φ with φ H, apply unit_of_sqr, calc
        φ 1 * φ 1 = φ (1 * 1) : (H 1 1)⁻¹
              ... = φ 1       : φ # unit_sqr⁻¹
    end

    @[hott] def homo_respects_inv (x : α) : φ.fst x⁻¹ = (φ.fst x)⁻¹ := begin
      cases φ with φ H, calc
        φ x⁻¹ = φ x⁻¹ * 1               : (monoid.mul_one (φ x⁻¹))⁻¹
          ... = φ x⁻¹ * (φ x * (φ x)⁻¹) : (λ y, φ x⁻¹ * y) # (group.mul_right_inv (φ x))⁻¹
          ... = φ x⁻¹ * φ x * (φ x)⁻¹   : (semigroup.mul_assoc _ _ _)⁻¹
          ... = φ (x⁻¹ * x) * (φ x)⁻¹   : (* (φ x)⁻¹) # (H x⁻¹ x)⁻¹
          ... = φ 1 * (φ x)⁻¹           : (λ y, φ y * (φ x)⁻¹) # (group.mul_left_inv x)
          ... = 1 * (φ x)⁻¹             : (* (φ x)⁻¹) # (homo_saves_unit ⟨φ, H⟩)
          ... = (φ x)⁻¹                 : monoid.one_mul (φ x)⁻¹
    end

    @[hott] def homo_respects_div (x y : α) : φ.fst (x / y) = φ.fst x / φ.fst y := begin
      cases φ with φ H, calc
        φ (x / y) = φ x * φ y⁻¹   : H x y⁻¹
              ... = φ x * (φ y)⁻¹ : (λ y, φ x * y) # (homo_respects_inv ⟨φ, H⟩ y)
              ... = φ x / φ y     : by trivial
    end

    @[hott] instance ker_is_subgroup : is_subgroup (ker φ) :=
    { unit := by apply homo_saves_unit,
      mul := begin
        intros a b h g, change _ = _,
        transitivity, { apply φ.snd }, symmetry,
        transitivity, { apply unit_sqr },
        apply mul_uniq, exact h⁻¹, exact g⁻¹
      end,
      inv := begin
        intros x h, change _ = _,
        cases φ with φ H, calc
          φ x⁻¹ = (φ x)⁻¹ : homo_respects_inv ⟨φ, H⟩ x
            ... = 1⁻¹     : has_inv.inv # h
            ... = 1       : unit_inv⁻¹
      end }

    instance ker_is_normal_subgroup : is_normal_subgroup (ker φ) := begin
      apply is_normal_subgroup.mk, intros n g G, cases φ with φ H,
      change _ = _ at G, have F := (H n g)⁻¹ ⬝ G, calc
        φ (g * n) = φ g * φ n     : H g n
              ... = φ g * (φ g)⁻¹ : (λ y, φ g * y) # (eq_inv_of_mul_eq_one F)
              ... = 1 : by apply mul_right_inv
    end

    instance im_is_subgroup : is_subgroup (im φ) :=
    { unit := ground_zero.HITs.merely.elem ⟨1, homo_saves_unit φ⟩,
      mul := begin
        intros a b G' H', fapply ground_zero.HITs.merely.rec _ _ G',
        { apply ground_zero.HITs.merely.uniq },
        { intro G,
          { fapply ground_zero.HITs.merely.rec _ _ H',
            { apply ground_zero.HITs.merely.uniq },
            { intro H, induction G with x G,
              induction H with y H,
              apply ground_zero.HITs.merely.elem,
              existsi (x * y), transitivity, apply φ.snd,
              induction G, induction H, trivial } } }
      end,
      inv := begin
        intros x H', fapply ground_zero.HITs.merely.rec _ _ H',
        { apply ground_zero.HITs.merely.uniq },
        { intro H, apply ground_zero.HITs.merely.elem,
          induction H with y H, existsi y⁻¹,
          transitivity, apply homo_respects_inv,
          apply map, assumption }
      end }
  end

  section
    variables {φ : set α} [is_subgroup φ]

    @[hott] def subgroup.mul (x y : φ.subtype) : φ.subtype := begin
      induction x with x H, induction y with y G,
      existsi (x * y), apply is_subgroup.mul; assumption
    end
    instance subtype_mul : has_mul φ.subtype := ⟨subgroup.mul⟩

    @[hott] def subgroup.inv (x : φ.subtype) : φ.subtype := begin
      induction x with x H, existsi x⁻¹,
      apply is_subgroup.inv, assumption
    end
    instance subtype_inv : has_inv φ.subtype := ⟨subgroup.inv⟩

    @[hott] def subgroup.unit : φ.subtype := ⟨1, is_subgroup.unit φ⟩
    instance subtype_unit : has_one φ.subtype := ⟨subgroup.unit⟩

    @[hott] def subgroup.set : hset φ.subtype :=
    begin apply set.hset, apply magma.set end

    @[hott] def subgroup.mul_assoc (x y z : φ.subtype) : x * y * z = x * (y * z) := begin
      induction x with x A, induction y with y B, induction z with z C,
      fapply ground_zero.types.sigma.prod,
      apply semigroup.mul_assoc, apply φ.snd
    end

    @[hott] def subgroup.one_mul (x : φ.subtype) : 1 * x = x := begin
      induction x with x H,
      fapply ground_zero.types.sigma.prod,
      apply monoid.one_mul, apply φ.snd
    end

    @[hott] def subgroup.mul_one (x : φ.subtype) : x * 1 = x := begin
      induction x with x H,
      fapply ground_zero.types.sigma.prod,
      apply monoid.mul_one, apply φ.snd
    end

    @[hott] def subgroup.mul_left_inv (x : φ.subtype) : x⁻¹ * x = 1 := begin
      induction x with x H,
      fapply ground_zero.types.sigma.prod,
      apply group.mul_left_inv, apply φ.snd
    end

    @[hott] instance subgroup.is_group : group φ.subtype :=
    { set := λ _ _, subgroup.set,
      mul_assoc := subgroup.mul_assoc,
      one_mul := subgroup.one_mul,
      mul_one := subgroup.mul_one,
      mul_left_inv := subgroup.mul_left_inv }
  end

  @[hott] def homo.surj {α : Type u} [group α]
    (φ : set α) [is_subgroup φ] : φ.subtype ⤳ α :=
  ⟨sigma.fst, λ ⟨a, _⟩ ⟨b, _⟩, ground_zero.types.eq.refl (a * b)⟩
end group

end ground_zero.algebra