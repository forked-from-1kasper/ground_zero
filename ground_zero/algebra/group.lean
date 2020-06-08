import ground_zero.HITs.quotient ground_zero.types.integer
import ground_zero.theorems.functions ground_zero.theorems.prop
open ground_zero.types.equiv (biinv transport)
open ground_zero.types.eq (map)
open ground_zero.structures
open ground_zero.types
open ground_zero.proto

namespace ground_zero.algebra
universes u v w

hott theory

def set (α : Type u) := Σ (φ : α → Type v), Π x, prop (φ x)
def set.contains {α : Type u} (x : α) (s : set α) : Type v := s.fst x
infix ∈ := set.contains

def set.prop {α : Type u} (x : α) (s : set α) : prop (x ∈ s) := s.snd x
def set.subtype {α : Type u} (s : set α) := Σ x, s.fst x

def set.univ (α : Type u) : set α :=
⟨λ _, 𝟏, λ _, unit_is_prop⟩

def set.inter {α : Type u} (a b : set α) : set α :=
⟨λ x, x ∈ a × x ∈ b, begin
  intro x, apply ground_zero.structures.product_prop;
  apply set.prop
end⟩

instance {α : Type u} : has_inter (set α) := ⟨set.inter⟩

@[hott] def set.hset {α : Type u} (s : set α) : hset α → hset s.subtype := begin
  intro H, apply zero_eqv_set.forward,
  fapply ground_zero.structures.ntype_respects_sigma 0,
  { apply zero_eqv_set.left, intros a b, apply H },
  { intro x, apply zero_eqv_set.left,
    apply prop_is_set, apply s.snd }
end

@[hott] def hset_equiv {α : Type u} (h : hset α) : hset (α ≃ α) := begin
  apply zero_eqv_set.forward,
  fapply ground_zero.structures.ntype_respects_sigma 0,
  { apply ground_zero.structures.pi_respects_ntype 0,
    intro x, apply zero_eqv_set.left, assumption },
  { intro x, apply zero_eqv_set.left, apply prop_is_set,
    apply ground_zero.theorems.prop.biinv_prop }
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

  @[hott] def mul_eq_one_of_inv_eq {x y : α} (h : x⁻¹ = y) : x * y = 1 :=
  (has_mul.mul x # h)⁻¹ ⬝ (mul_right_inv x)

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
    variables {μ : Type u} {η : Type v} (φ : μ → η)
    def im.aux := ground_zero.theorems.functions.fib_inh φ
    def im : set η := ⟨im.aux φ, λ _, ground_zero.HITs.merely.uniq⟩
  end

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
      [group α] [group β] [group φ]
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
    def Im  := (im φ.fst).subtype
  end

  @[hott] def iso (α : Type u) (β : Type v) [group α] [group β] :=
  Σ (f : α → β), respects_mul f × biinv f
  infix ` ≅ `:25 := iso

  @[hott, refl] def iso.refl (α : Type u) [group α] : α ≅ α := begin
    existsi id, split,
    { intros a b, trivial },
    { split; existsi id; intro x; reflexivity }
  end

  @[hott, symm] def iso.symm {α : Type u} {β : Type v}
    [group α] [group β] : α ≅ β → β ≅ α
  | ⟨f, ⟨F, (⟨g, G⟩, ⟨h, H⟩)⟩⟩ := begin
    have G' := qinv.rinv_inv f h g H G,
    existsi g, split,
    { intros a b, symmetry, transitivity,
      { symmetry, apply G }, transitivity,
      { apply map g, apply F }, transitivity,
      { apply map g, apply map (* f (g b)), apply G' },
      { apply map g, apply map (has_mul.mul a), apply G' } },
    { split; existsi f, apply G', apply G }
  end

  @[hott, trans] def iso.trans {α : Type u} {β : Type v} {γ : Type w}
    [group α] [group β] [group γ] : α ≅ β → β ≅ γ → α ≅ γ
  | ⟨f, ⟨F, e₁⟩⟩ ⟨g, ⟨G, e₂⟩⟩ := begin
    existsi g ∘ f, split,
    { intros a b, transitivity, { apply map g, apply F },
      transitivity, apply G, reflexivity },
    { apply equiv.biinv_trans e₁ e₂ }
  end

  @[hott] def iso.of_equiv {α : Type u} {β : Type v} [group α] [group β] :
    Π (e : α ≃ β), respects_mul e.forward → α ≅ β
  | ⟨f, e⟩ h := ⟨f, (h, e)⟩

  @[hott] def iso.of_homo {α : Type u} {β : Type v} [group α] [group β] :
    Π (φ : α ⤳ β), biinv φ.fst → α ≅ β
  | ⟨f, h⟩ e := ⟨f, (h, e)⟩

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

  @[hott] def x_mul_inv_y_inv (x y : α) := calc
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
      { intro x, change ground_zero.HITs.quotient.elem _ = _,
        apply map, apply monoid.one_mul },
      { intros, apply ground_zero.HITs.quotient.set }
    end

    @[hott] noncomputable def factor.assoc (x y z : α/φ) : x * y * z = x * (y * z) := begin
      fapply ground_zero.HITs.quotient.ind_prop _ _ x; clear x,
      { fapply ground_zero.HITs.quotient.ind_prop _ _ y; clear y,
        { fapply ground_zero.HITs.quotient.ind_prop _ _ z; clear z,
          { intros z y x, change ground_zero.HITs.quotient.elem _ = _,
            apply map, apply semigroup.mul_assoc },
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
      { intro x, change ground_zero.HITs.quotient.elem _ = _,
        apply map, apply mul_left_inv },
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

    @[hott] instance ker_is_normal_subgroup : is_normal_subgroup (ker φ) := begin
      apply is_normal_subgroup.mk, intros n g G, cases φ with φ H,
      change _ = _ at G, have F := (H n g)⁻¹ ⬝ G, calc
        φ (g * n) = φ g * φ n     : H g n
              ... = φ g * (φ g)⁻¹ : (λ y, φ g * y) # (eq_inv_of_mul_eq_one F)
              ... = 1 : by apply mul_right_inv
    end

    @[hott] instance im_is_subgroup : is_subgroup (im φ.fst) :=
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

  @[hott] def subgroup.inter (φ : set α) (ψ : set α)
    [is_subgroup φ] [is_subgroup ψ] : set ψ.subtype :=
  ⟨λ x, x.fst ∈ φ, λ x, set.prop x.fst φ⟩

  @[hott] instance subgroup_subgroup (φ : set α) (ψ : set α)
    [is_subgroup φ] [is_subgroup ψ] :
    is_subgroup (subgroup.inter φ ψ) := begin
    split, { change 1 ∈ φ, apply is_subgroup.unit },
    { intros a b G H, induction a with a g,
      induction b with b h, change _ ∈ φ,
      apply is_subgroup.mul; assumption },
    { intros a G, induction a with a g,
      change _ ∈ φ, apply is_subgroup.inv,
      assumption }
  end

  @[hott] instance abelian_subgroup_is_normal {α : Type u} [abelian α]
    (φ : set α) [is_subgroup φ] : is_normal_subgroup φ := begin
    split, intros g h p, apply transport (∈ φ),
    apply abelian.mul_comm, assumption
  end

  @[hott] instance abelian_subgroup_is_abelian {α : Type u} [abelian α]
    (φ : set α) [is_subgroup φ] : abelian φ.subtype := begin
    split, intros a b, induction a with a g, induction b with b h,
    fapply ground_zero.types.sigma.prod,
    { apply abelian.mul_comm }, { apply φ.snd }
  end

  @[hott] def homo.surj {α : Type u} [group α]
    (φ : set α) [is_subgroup φ] : φ.subtype ⤳ α :=
  ⟨sigma.fst, λ ⟨a, _⟩ ⟨b, _⟩, ground_zero.types.eq.refl (a * b)⟩

  inductive D₃
  | R₀ | R₁ | R₂
  | S₀ | S₁ | S₂
  open D₃

  @[hott] def D₃.inv : D₃ → D₃
  | R₀ := R₀ | R₁ := R₂ | R₂ := R₁
  | S₀ := S₀ | S₁ := S₁ | S₂ := S₂

  @[hott] def D₃.mul : D₃ → D₃ → D₃
  | R₀ R₀ := R₀ | R₀ R₁ := R₁ | R₀ R₂ := R₂
  | R₀ S₀ := S₀ | R₀ S₁ := S₁ | R₀ S₂ := S₂
  | R₁ R₀ := R₁ | R₁ R₁ := R₂ | R₁ R₂ := R₀
  | R₁ S₀ := S₁ | R₁ S₁ := S₂ | R₁ S₂ := S₀
  | R₂ R₀ := R₂ | R₂ R₁ := R₀ | R₂ R₂ := R₁
  | R₂ S₀ := S₂ | R₂ S₁ := S₀ | R₂ S₂ := S₁
  | S₀ R₀ := S₀ | S₀ R₁ := S₂ | S₀ R₂ := S₁
  | S₀ S₀ := R₀ | S₀ S₁ := R₂ | S₀ S₂ := R₁
  | S₁ R₀ := S₁ | S₁ R₁ := S₀ | S₁ R₂ := S₂
  | S₁ S₀ := R₁ | S₁ S₁ := R₀ | S₁ S₂ := R₂
  | S₂ R₀ := S₂ | S₂ R₁ := S₁ | S₂ R₂ := S₀
  | S₂ S₀ := R₂ | S₂ S₁ := R₁ | S₂ S₂ := R₀

  @[hott] instance D₃.has_one : has_one D₃ := ⟨R₀⟩
  @[hott] instance D₃.has_inv : has_inv D₃ := ⟨D₃.inv⟩
  @[hott] instance D₃.has_mul : has_mul D₃ := ⟨D₃.mul⟩

  def D₃.elim {β : Type u} : β → β → β → β → β → β → D₃ → β :=
  @D₃.rec (λ _, β)

  @[hott] instance D₃.is_magma : magma D₃ := begin
    split, apply ground_zero.structures.Hedberg,
    intros x y, induction x; induction y;
    try { apply sum.inl, refl },
    repeat { apply sum.inr, intro p, apply ff_neq_tt, symmetry },
    repeat { apply (D₃.elim tt ff ff ff ff ff) # p },
    repeat { apply (D₃.elim ff tt ff ff ff ff) # p },
    repeat { apply (D₃.elim ff ff tt ff ff ff) # p },
    repeat { apply (D₃.elim ff ff ff tt ff ff) # p },
    repeat { apply (D₃.elim ff ff ff ff tt ff) # p },
    repeat { apply (D₃.elim ff ff ff ff ff tt) # p }
  end

  @[hott] instance D₃.semigroup : semigroup D₃ := begin
    split, intros a b c,
    induction a; induction b; induction c; trivial
  end

  @[hott] instance D₃.monoid : monoid D₃ :=
  begin split; intro a; induction a; trivial end

  @[hott] instance D₃.group : group D₃ :=
  begin split, intro a, induction a; trivial end

  @[hott] def A₃ : set D₃ :=
  ⟨D₃.elim 𝟏 𝟏 𝟏 𝟎 𝟎 𝟎, begin
    intros x, induction x,
    repeat { apply ground_zero.structures.unit_is_prop },
    repeat { apply ground_zero.structures.empty_is_prop }
  end⟩

  @[hott] instance A₃.subgroup : is_subgroup A₃ := begin
    split, { apply ★ },
    { intros a b p q, induction a; induction b;
      induction p; induction q; apply ★ },
    { intros a p, induction a; induction p; apply ★ }
  end

  @[hott] instance A₃.normal_subgroup : is_normal_subgroup A₃ := begin
    split, intros g h p; induction g; induction h;
    induction p; apply ★
  end

  def Z₂ := bool
  def Z₂.mul := bxor
  def Z₂.inv := @ground_zero.proto.idfun Z₂

  @[hott] instance Z₂.has_one : has_one Z₂ := ⟨ff⟩
  @[hott] instance Z₂.has_inv : has_inv Z₂ := ⟨Z₂.inv⟩
  @[hott] instance Z₂.has_mul : has_mul Z₂ := ⟨Z₂.mul⟩

  @[hott] instance : magma Z₂ := begin
    split, apply ground_zero.structures.Hedberg,
    intros x y, induction x; induction y; try { apply sum.inl, refl },
    repeat { apply sum.inr, intro p, apply ff_neq_tt },
    exact p, exact p⁻¹
  end

  @[hott] instance Z₂.semigroup : semigroup Z₂ := begin
    split, intros a b c,
    induction a; induction b; induction c; trivial
  end

  @[hott] instance Z₂.monoid : monoid Z₂ :=
  begin split; intro a; induction a; trivial end

  @[hott] instance Z₂.group : group Z₂ :=
  begin split, intro a, induction a; trivial end

  def D₃.inj : D₃ → D₃/A₃ := factor.incl

  @[hott] def Z₂.encode : Z₂ → D₃/A₃
  | ff := D₃.inj R₀
  | tt := D₃.inj S₀

  @[hott] def Z₂.decode : D₃/A₃ → Z₂ := begin
    fapply ground_zero.HITs.quotient.rec,
    { exact D₃.elim ff ff ff tt tt tt },
    { intros x y H; induction x; induction y; induction H; trivial },
    { apply magma.set }
  end

  @[hott] noncomputable def Z₂.iso : Z₂ ≅ D₃/A₃ := begin
    existsi Z₂.encode, split,
    { intros x y, induction x; induction y; trivial },
    split; existsi Z₂.decode,
    { intro x, induction x; trivial },
    { fapply ground_zero.HITs.quotient.ind,
      { intro x, induction x; apply ground_zero.HITs.quotient.sound; exact ★ },
      { intros x y H, apply magma.set },
      { intro x, apply ground_zero.structures.prop_is_set,
        apply magma.set } }
  end

  @[hott] def triv : set α :=
  ⟨λ x, 1 = x, begin intro x, apply magma.set end⟩

  @[hott] instance triv.subgroup : @is_subgroup α _ triv := begin
    split,
    { change _ = _, reflexivity },
    { intros a b p q,
      change _ = _ at p, change _ = _ at q,
      induction p, induction q,
      change _ = _, symmetry,
      apply monoid.mul_one },
    { intros a p, change _ = _ at p,
      induction p, change _ = _,
      apply unit_inv }
  end

  @[hott] instance triv.normal_subgroup : @is_normal_subgroup α _ triv := begin
    split, intros g h p, change _ = _ at p,
    change _ = _, apply @mul_cancel_left α _ _ _ g,
    transitivity, apply monoid.mul_one,
    transitivity, { symmetry, apply monoid.one_mul },
    symmetry, transitivity, { symmetry, apply semigroup.mul_assoc },
    symmetry, apply ground_zero.types.eq.map (* g),
    assumption
  end

  @[hott] def triv.encode : α → α/triv := factor.incl
  @[hott] def triv.decode : α/triv → α := begin
    fapply ground_zero.HITs.quotient.rec,
    exact id,
    { intros x y H, change _ = _ at H,
      change _ = _ * _ at H,
      apply inv_inj, apply eq_inv_of_mul_eq_one,
      exact H⁻¹ },
    apply magma.set
  end

  @[hott] noncomputable def triv.factor : α ≅ α/triv := begin
    existsi triv.encode, split,
    { intros x y, reflexivity },
    split; existsi triv.decode,
    { intro x, reflexivity },
    { fapply ground_zero.HITs.quotient.ind_prop; intro x,
      { reflexivity },
      { apply magma.set } }
  end

  inductive exp (α : Type u)
  | unit {} : exp
  | elem {} : α → exp
  | mul  {} : exp → exp → exp
  | inv  {} : exp → exp

  namespace exp
    @[hott] def eval {α : Type u} {β : Type v} [group β]
      (f : α → β) : exp α → β
    | unit      := 1
    | (elem x)  := f x
    | (mul x y) := eval x * eval y
    | (inv x)   := (eval x)⁻¹
  end exp

  private structure F.aux (α : Type u) :=
  (val : exp α)

  def F (α : Type u) := F.aux α

  namespace F
    variables {ε : Type u}
    attribute [nothott] F.aux.rec_on F.aux.rec aux.val

    @[hott] def unit : F ε := ⟨exp.unit⟩
    @[hott] def elem : ε → F ε := λ x, ⟨exp.elem x⟩

    @[safe] def mul (x y : F ε) : F ε := ⟨exp.mul x.val y.val⟩
    @[safe] def inv (x : F ε)   : F ε := ⟨exp.inv x.val⟩

    @[safe] def rec {α : Type u} [group α] (f : ε → α) (x : F ε) : α :=
    exp.eval f x.val

    attribute [irreducible] F

    instance : has_one (F ε) := ⟨unit⟩
    instance : has_mul (F ε) := ⟨mul⟩
    instance : has_inv (F ε) := ⟨inv⟩

    axiom mul_assoc (a b c : F ε) : (a * b) * c = a * (b * c)
    axiom one_mul       (a : F ε) : 1 * a = a
    axiom mul_one       (a : F ε) : a * 1 = a
    axiom mul_left_inv  (a : F ε) : a⁻¹ * a = 1

    axiom set : hset (F ε)

    noncomputable instance : magma (F ε) :=
    begin split, apply set end

    noncomputable instance : semigroup (F ε) :=
    begin split, apply mul_assoc end

    noncomputable instance : monoid (F ε) :=
    begin split, apply one_mul, apply mul_one end

    noncomputable instance : group (F ε) :=
    begin split, apply mul_left_inv end

    noncomputable def homomorphism {α : Type u} [group α] (f : ε → α) : F ε ⤳ α :=
    ⟨rec f, begin intros x y, reflexivity end⟩

    noncomputable def recβrule₁ {a b c : F ε} (f : ε → α) :
      rec f # (mul_assoc a b c) =
        semigroup.mul_assoc (rec f a) (rec f b) (rec f c) :=
    by apply magma.set
    noncomputable def recβrule₂ {a : F ε} (f : ε → α) :
      rec f # (one_mul a) = monoid.one_mul (rec f a) :=
    by apply magma.set
    noncomputable def recβrule₃ {a : F ε} (f : ε → α) :
      rec f # (mul_one a) = monoid.mul_one (rec f a) :=
    by apply magma.set
    noncomputable def recβrule₄ {a : F ε} (f : ε → α) :
      rec f # (mul_left_inv a) = group.mul_left_inv (rec f a) :=
    by apply magma.set
  end F

  @[hott] def zentrum (α : Type u) [group α] : set α :=
  ⟨λ z, Π g, z * g = g * z, begin
    intros x p q, apply ground_zero.theorems.funext,
    intro y, apply magma.set
  end⟩

  @[hott] instance zentrum_is_subgroup : is_subgroup (zentrum α) := begin
    split,
    { intro x, transitivity,
      { apply monoid.one_mul },
      { symmetry, apply monoid.mul_one } },
    { intros a b g h c, symmetry, calc
        c * (a * b) = (c * a) * b : (semigroup.mul_assoc _ _ _)⁻¹
                ... = (a * c) * b : (* b) # (g c)⁻¹
                ... = a * (c * b) : semigroup.mul_assoc _ _ _
                ... = a * (b * c) : (has_mul.mul a) # (h c)⁻¹
                ... = a * b * c   : (semigroup.mul_assoc _ _ _)⁻¹ },
    { intros a g b, calc
      a⁻¹ * b = a⁻¹ * b⁻¹⁻¹ : (has_mul.mul a⁻¹) # (inv_inv b)⁻¹
          ... = (b⁻¹ * a)⁻¹ : (inv_explode _ _)⁻¹
          ... = (a * b⁻¹)⁻¹ : has_inv.inv # (g b⁻¹)⁻¹
          ... = b⁻¹⁻¹ * a⁻¹ : inv_explode _ _
          ... = b * a⁻¹     : (* a⁻¹) # (inv_inv b) }
  end

  @[hott] instance zentrum_is_normal : is_normal_subgroup (zentrum α) := begin
    split, intros g h G z,
    have p := (semigroup.mul_assoc g h g)⁻¹ ⬝ G g,
    have q := mul_cancel_left p,
    transitivity, { apply map (* z), apply q },
    symmetry, transitivity, { apply map (has_mul.mul z), apply q },
    symmetry, apply G
  end

  @[hott] instance univ_is_subgroup : is_subgroup (set.univ α) :=
  begin split; intros; apply ★ end

  @[hott] instance univ_is_normal : is_normal_subgroup (set.univ α) :=
  begin split, intros, apply ★ end

  @[hott] instance unit_mul : has_mul 𝟏 :=
  begin split, intros, apply ★ end

  @[hott] instance unit_magma : magma 𝟏 :=
  begin split, apply unit_is_set end

  @[hott] instance unit_semigroup : semigroup 𝟏 :=
  begin split, intros, reflexivity end

  @[hott] instance unit_has_one : has_one 𝟏 := ⟨★⟩

  @[hott] instance unit_monoid : monoid 𝟏 :=
  begin split; intro x; induction x; reflexivity end

  @[hott] instance unit_has_inv : has_inv 𝟏 := ⟨λ _, ★⟩

  @[hott] instance unit_is_group : group 𝟏 :=
  begin split; intro x; reflexivity end

  @[hott] instance unit_is_abelian : abelian 𝟏 :=
  begin split, intros, reflexivity end

  def univ.decode : 𝟏 → α/set.univ α := λ _, 1

  @[hott] noncomputable def univ_contr : contr (α/set.univ α) := begin
    existsi univ.decode ★,
    fapply ground_zero.HITs.quotient.ind_prop; intro x,
    { apply ground_zero.HITs.quotient.sound, apply ★ },
    { apply magma.set }
  end

  @[hott] noncomputable def univ_prop : prop (α/set.univ α) :=
  contr_impl_prop univ_contr

  @[hott] noncomputable def univ_factor : 𝟏 ≅ α/set.univ α := begin
    existsi univ.decode, split,
    { intros x y, apply univ_prop },
    split; existsi (λ _, ★); intro x,
    apply unit_is_prop, apply univ_prop
  end

  @[hott] def identity.set {α : Type u} (H : hset α) : hset (identity α) :=
  begin apply hset_respects_equiv, apply equiv.identity_eqv, assumption end

  def Z := identity integer
  @[hott] instance Z.has_mul : has_mul Z := ⟨identity.lift₂ integer.add⟩
  @[hott] instance Z.has_one : has_one Z := ⟨identity.elem 0⟩
  @[hott] instance Z.has_inv : has_inv Z := ⟨identity.lift integer.negate⟩

  @[hott] noncomputable instance Z.magma : magma Z :=
  begin split, apply identity.set, apply integer.set end

  @[hott] def ker.encode {β : Type v} [group β] {φ : α ⤳ β} : α/ker φ → Im φ := begin
    fapply ground_zero.HITs.quotient.rec,
    { intro x, existsi φ.fst x, apply ground_zero.HITs.merely.elem,
      existsi x, trivial },
    { intros x y H, fapply ground_zero.types.sigma.prod,
      change _ = _ at H, transitivity, { symmetry, apply inv_inv },
      apply inv_eq_of_mul_eq_one, transitivity,
      { apply map (* φ.fst y), symmetry, apply homo_respects_inv },
      transitivity, { symmetry, apply φ.snd }, apply H,
      apply ground_zero.HITs.merely.uniq },
    { apply set.hset, apply magma.set }
  end

  @[hott] noncomputable def ker.encode_inj {β : Type v} [group β] {φ : α ⤳ β} :
    Π (x y : α/ker φ), ker.encode x = ker.encode y → x = y := begin
    intros x y, fapply ground_zero.HITs.quotient.ind_prop _ _ x; clear x; intro x,
    { fapply ground_zero.HITs.quotient.ind_prop _ _ y; clear y; intro y,
      { intro p, apply ground_zero.HITs.quotient.sound,
        change _ = _, transitivity, apply φ.snd,
        transitivity, { apply eq.map (* φ.fst y), apply homo_respects_inv },
        apply mul_eq_one_of_inv_eq,
        transitivity, apply inv_inv,
        apply (ground_zero.types.sigma.sigma_eq_of_eq p).fst },
      { apply impl_prop, apply magma.set } },
    { apply impl_prop, apply magma.set }
  end

  @[hott] noncomputable def ker.decode_sigma {β : Type v} [group β] {φ : α ⤳ β} :
    Π (x : Im φ), (Σ (y : α/ker φ), ker.encode y = x) := begin
    intro x, induction x with x H,
    fapply ground_zero.HITs.merely.ind _ _ H; intro z,
    { induction z with z p, existsi factor.incl z,
      fapply ground_zero.types.sigma.prod, apply p,
      apply ground_zero.HITs.merely.uniq },
    { intros u v, induction u with u H, induction v with v G,
      fapply ground_zero.types.sigma.prod,
      { apply ker.encode_inj, transitivity, exact H,
        symmetry, exact G },
      { apply set.hset, apply magma.set } }
  end

  @[hott] noncomputable def ker.decode {β : Type v} [group β] {φ : α ⤳ β}
    (x : Im φ) : α/ker φ :=
  (ker.decode_sigma x).fst

  instance im.subgroup {β : Type v} [group β] {φ : α ⤳ β} : group (Im φ) :=
  by apply @subgroup.is_group _ _ (im φ.fst) _

  -- Fundamental theorem on homomorphisms
  @[hott] noncomputable def first_homo_theorem {β : Type v} [group β]
    {φ : α ⤳ β} : Im φ ≅ α/ker φ := begin
    existsi ker.decode, split,
    { intros a b, induction a with a A, induction b with b B,
      change ∥_∥ at A, change ∥_∥ at B,
      fapply ground_zero.HITs.merely.ind _ _ A; clear A; intro A,
      { fapply ground_zero.HITs.merely.ind _ _ B; clear B; intro B,
        { induction A, induction B, reflexivity },
        { apply magma.set } },
      { apply magma.set } },
    split; existsi ker.encode,
    { intro x, apply (ker.decode_sigma x).snd },
    { fapply ground_zero.HITs.quotient.ind_prop,
      { intro x, trivial },
      { intro x, apply magma.set } }
  end

  @[hott] instance inter_subgroup (φ ψ : set α)
    [is_subgroup φ] [is_subgroup ψ] : is_subgroup (φ ∩ ψ) := begin
    split, { split; apply is_subgroup.unit },
    { intros a b p q,
      induction p with p₁ p₂,
      induction q with q₁ q₂,
      split; apply is_subgroup.mul; assumption },
    { intros a h, induction h with u v,
      split; apply is_subgroup.inv; assumption }
  end

  @[hott] def mul (φ ψ : set α) : set α :=
  ⟨λ a, ∥(Σ x y, x ∈ φ × y ∈ ψ × x * y = a)∥,
   λ _, ground_zero.HITs.merely.uniq⟩

  -- Permutations
  @[hott] def S (α : 0-Type) := α.fst ≃ α.fst

  section
    variables {ε : 0-Type}
    @[hott] def S.mul (p q : S ε) := equiv.trans p q
    @[hott] def S.one             := equiv.id ε.fst
    @[hott] def S.inv (p : S ε)   := equiv.symm p

    @[hott] instance S.has_mul : has_mul (S ε) := ⟨S.mul⟩
    @[hott] instance S.has_one : has_one (S ε) := ⟨S.one⟩
    @[hott] instance S.has_inv : has_inv (S ε) := ⟨S.inv⟩

    @[hott] instance S.magma : magma (S ε) :=
    begin split, apply hset_equiv, apply zero_eqv_set.forward, exact ε.snd end

    @[hott] instance S.semigroup : semigroup (S ε) := begin
      split, intros, fapply sigma.prod,
      { apply ground_zero.theorems.funext, intro x,
        induction a, induction b, induction c,
        reflexivity },
      { apply ground_zero.theorems.prop.biinv_prop }
    end

    @[hott] instance S.monoid : monoid (S ε) := begin
      split; intros; fapply sigma.prod,
      repeat { apply ground_zero.theorems.funext, intro x,
               induction a, reflexivity },
      repeat { apply ground_zero.theorems.prop.biinv_prop }
    end

    @[hott] instance S.group : group (S ε) := begin
      split, intros, fapply sigma.prod,
      { apply ground_zero.theorems.funext, intro x,
        induction a with f e, induction e with e₁ e₂,
        induction e₁ with g G, induction e₂ with h H,
        change f _ = x, apply H },
      { apply ground_zero.theorems.prop.biinv_prop }
    end
  end

  @[hott] def op (α : Type u) [group α] := identity α
  postfix `ᵒᵖ`:2000 := op

  @[hott] def op.mul : αᵒᵖ → αᵒᵖ → αᵒᵖ
  | ⟨x⟩ ⟨y⟩ := ⟨y * x⟩
  @[hott] def op.inv : αᵒᵖ → αᵒᵖ
  | ⟨x⟩ := ⟨x⁻¹⟩
  @[hott] def op.one : αᵒᵖ := ⟨1⟩

  @[hott] instance op.has_mul : has_mul αᵒᵖ := ⟨op.mul⟩
  @[hott] instance op.has_inv : has_inv αᵒᵖ := ⟨op.inv⟩
  @[hott] instance op.has_one : has_one αᵒᵖ := ⟨op.one⟩

  @[hott] instance op.magma : magma αᵒᵖ :=
  begin split, apply identity.set, apply magma.set end

  @[hott] instance op.semigroup : semigroup αᵒᵖ := begin
    split, intros, cases a, cases b, cases c,
    apply eq.map identity.elem,
    symmetry, apply semigroup.mul_assoc
  end

  @[hott] instance op.monoid : monoid αᵒᵖ := begin
    split; intros; cases a; apply eq.map identity.elem,
    apply monoid.mul_one, apply monoid.one_mul
  end

  @[hott] instance op.group : group αᵒᵖ := begin
    split, intros, cases a,
    apply eq.map identity.elem, apply mul_right_inv
  end

  @[hott] def op.elim : αᵒᵖ → α
  | ⟨x⟩ := x⁻¹

  @[hott] def op.intro : α → αᵒᵖ :=
  λ x, identity.elem x⁻¹

  @[hott] def op.univ : α ⤳ αᵒᵖ :=
  ⟨op.intro, begin intros a b, apply eq.map identity.elem, apply inv_explode end⟩

  @[hott] def op.iso : α ≅ αᵒᵖ := begin
    fapply iso.of_homo, exact op.univ,
    split; existsi op.elim; intro x,
    { apply inv_inv },
    { induction x, apply eq.map identity.elem, apply inv_inv }
  end
end group

end ground_zero.algebra