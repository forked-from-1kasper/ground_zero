import ground_zero.theorems.functions ground_zero.algebra.basic
open ground_zero.types.equiv (bimap biinv transport)
open ground_zero.types.Id (map)
open ground_zero.structures
open ground_zero.types
open ground_zero.proto
open ground_zero

/-
  Basic lemmas about groups and abelian groups.

  Homomorphism properties.

  ℤ₁ and ℤ₂ groups.

  Opposite group.
  * https://en.wikipedia.org/wiki/Opposite_group
-/

namespace ground_zero.algebra
universes u v u' v' w

hott theory

section
  variables {μ : Type u} {η : Type v} (φ : μ → η)
  def im.aux := ground_zero.theorems.functions.fib_inh φ
  def im : ens η := ⟨im.aux φ, λ _, HITs.merely.uniq⟩

  def im.intro (m : μ): φ m ∈ im φ :=
  begin apply HITs.merely.elem, existsi m, reflexivity end

  def im.inh (m : μ) : (im φ).inh :=
  begin apply HITs.merely.elem, existsi φ m, apply im.intro end
end

namespace pregroup
  variable (G : pregroup)
  @[hott] def isproper (x : G.carrier) := neq x G.e

  @[hott] def proper := Σ x, G.isproper x

  @[hott] def proper.prop {x : G.carrier} : prop (G.isproper x) :=
  structures.impl_prop structures.empty_is_prop
end pregroup

namespace pregroup
  variable {G : pregroup}
  def conjugate (a x : G.carrier) := G.φ (G.φ (G.ι x) a) x

  def conjugate_rev (a x : G.carrier) := G.φ (G.φ x a) (G.ι x)

  def right_div (x y : G.carrier) := G.φ x (G.ι y)
  def left_div  (x y : G.carrier) := G.φ (G.ι x) y

  def is_subgroup (G : pregroup) (φ : G.subset) :=
  (G.e ∈ φ) × (Π a b, a ∈ φ → b ∈ φ → G.φ a b ∈ φ) × (Π a, a ∈ φ → G.ι a ∈ φ)
  def subgroup (G : pregroup) := Σ φ, is_subgroup G φ

  def subgroup.set (φ : G.subgroup) : ens G.carrier := φ.fst
  def subgroup.subtype (φ : G.subgroup) := φ.set.subtype

  def subgroup.mem (x : G.carrier) (φ : G.subgroup) := x ∈ φ.set
  infix ∈ := subgroup.mem

  def subgroup.ssubset (φ ψ : G.subgroup) :=
  ens.ssubset φ.set ψ.set
  infix ⊆ := subgroup.ssubset

  def subgroup.unit (φ : G.subgroup) := φ.snd.fst
  def subgroup.mul  (φ : G.subgroup) := φ.snd.snd.fst
  def subgroup.inv  (φ : G.subgroup) := φ.snd.snd.snd

  def subgroup.mk (φ : G.subset) (α : G.e ∈ φ)
    (β : Π a b, a ∈ φ → b ∈ φ → G.φ a b ∈ φ)
    (γ : Π a, a ∈ φ → G.ι a ∈ φ) : subgroup G :=
  ⟨φ, (α, β, γ)⟩
end pregroup

namespace group
  open ground_zero.algebra.pregroup (right_div left_div conjugate conjugate_rev subgroup)

  variables {G : pregroup} [group G]
  local infix ` * `  := G.φ
  local notation `e` := G.e
  local postfix ⁻¹   := G.ι

  @[hott] def left_unit_uniq (e' : G.carrier) (one_mul' : Π a, e' * a = a) : e' = e :=
  Id.inv (G.mul_one e') ⬝ one_mul' e

  @[hott] def right_unit_uniq (e' : G.carrier) (mul_one' : Π a, a * e' = a) : e' = e :=
  Id.inv (G.one_mul e') ⬝ mul_one' e

  @[hott] def unit_of_sqr {x : G.carrier} (h : x * x = x) := calc
      x = e * x         : Id.inv (G.one_mul _)
    ... = (x⁻¹ * x) * x : (* x) # (Id.inv $ G.mul_left_inv x)
    ... = x⁻¹ * (x * x) : G.mul_assoc _ _ _
    ... = x⁻¹ * x       : G.φ x⁻¹ # h
    ... = e             : G.mul_left_inv _

  @[hott] def inv_eq_of_mul_eq_one {x y : G.carrier} (h : x * y = e) := calc
     x⁻¹ = x⁻¹ * e       : Id.inv (G.mul_one _)
     ... = x⁻¹ * (x * y) : G.φ x⁻¹ # (Id.inv h)
     ... = (x⁻¹ * x) * y : Id.inv (G.mul_assoc _ _ _)
     ... = e * y         : (* y) # (G.mul_left_inv x)
     ... = y             : G.one_mul y

  @[hott] def inv_inv (x : G.carrier) : x⁻¹⁻¹ = x :=
  inv_eq_of_mul_eq_one (G.mul_left_inv x)

  @[hott] def eq_inv_of_mul_eq_one {x y : G.carrier} (h : x * y = e) : x = y⁻¹ :=
  Id.inv (inv_inv x) ⬝ G.ι # (inv_eq_of_mul_eq_one h)

  @[hott] def mul_right_inv (x : G.carrier) := calc
    x * x⁻¹ = x⁻¹⁻¹ * x⁻¹ : (* x⁻¹) # (Id.inv $ inv_inv x)
        ... = e           : G.mul_left_inv x⁻¹

  @[hott] def mul_eq_one_of_inv_eq {x y : G.carrier} (h : x⁻¹ = y) : x * y = e :=
  Id.inv (G.φ x # h) ⬝ (mul_right_inv x)

  @[hott] def inv_inj {x y : G.carrier} (h : x⁻¹ = y⁻¹) : x = y := calc
      x = x⁻¹⁻¹ : Id.inv (inv_inv x)
    ... = y⁻¹⁻¹ : G.ι # h
    ... = y     : inv_inv y

  @[hott] def mul_cancel_left {a b c : G.carrier} (h : c * a = c * b) := calc
      a = e * a         : Id.inv (G.one_mul a)
    ... = (c⁻¹ * c) * a : (* a) # (Id.inv $ G.mul_left_inv c)
    ... = c⁻¹ * (c * a) : G.mul_assoc _ _ _
    ... = c⁻¹ * (c * b) : G.φ c⁻¹ # h
    ... = (c⁻¹ * c) * b : Id.inv (G.mul_assoc _ _ _)
    ... = e * b         : (* b) # (G.mul_left_inv c)
    ... = b             : G.one_mul b

  @[hott] def mul_cancel_right {a b c : G.carrier} (h : a * c = b * c) := calc
      a = a * e         : Id.inv (G.mul_one a)
    ... = a * (c * c⁻¹) : (G.φ a) # (Id.inv $ mul_right_inv c)
    ... = (a * c) * c⁻¹ : Id.inv (G.mul_assoc _ _ _)
    ... = (b * c) * c⁻¹ : (* c⁻¹) # h
    ... = b * (c * c⁻¹) : G.mul_assoc _ _ _
    ... = b * e         : (G.φ b) # (mul_right_inv c)
    ... = b             : G.mul_one b

  @[hott] def unit_inv : e = e⁻¹ :=
  Id.inv (mul_right_inv e) ⬝ G.one_mul e⁻¹

  @[hott] def unit_sqr : e = e * e :=
  Id.inv (G.one_mul e)

  @[hott] def unit_commutes (x : G.carrier) : e * x = x * e :=
  (G.one_mul x) ⬝ Id.inv (G.mul_one x)

  @[hott] def unit_commutes_inv (x : G.carrier) : x * e = e * x :=
  Id.inv (unit_commutes x)

  @[hott] def inv_explode (x y : G.carrier) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
  inv_eq_of_mul_eq_one
    (calc (x * y) * (y⁻¹ * x⁻¹)
        = ((x * y) * y⁻¹) * x⁻¹ :
          Id.inv (G.mul_assoc _ _ _)
    ... = (x * e) * x⁻¹ :
          begin
            apply map (* x⁻¹), transitivity,
            { apply G.mul_assoc },
            { apply map, apply mul_right_inv }
          end
    ... = x * x⁻¹ : (* x⁻¹) # (G.mul_one x)
    ... = e : by apply mul_right_inv)

  @[hott] def sqr_unit {x : G.carrier} (p : x * x = e) := calc
      x = x * e         : Id.inv (G.mul_one x)
    ... = x * (x * x⁻¹) : (G.φ x) # (Id.inv $ mul_right_inv x)
    ... = (x * x) * x⁻¹ : Id.inv (G.mul_assoc x x x⁻¹)
    ... = e * x⁻¹       : (* x⁻¹) # p
    ... = x⁻¹           : G.one_mul x⁻¹

  @[hott] def sqr_unit_impls_abelian (H : Π x, x * x = e) : abelian G :=
  begin
    split, intros x y, have p := λ x, sqr_unit (H x), calc
      x * y = x⁻¹ * y⁻¹ : bimap G.φ (p x) (p y)
        ... = (y * x)⁻¹ : Id.inv (inv_explode y x)
        ... = y * x     : Id.inv (p _)
  end

  local infix ^ := @conjugate G
  local infix / := @right_div G

  @[hott] def eq_of_div_eq {x y : G.carrier}
    (h : @left_div G x y = e) : x = y :=
  Id.inv (inv_inv x) ⬝ (inv_eq_of_mul_eq_one h)

  @[hott] def eq_of_rdiv_eq {x y : G.carrier} (h : x / y = e) : x = y :=
  inv_inj (inv_eq_of_mul_eq_one h)

  @[hott] def cancel_left (a b : G.carrier) := calc
      a = a * e         : Id.inv (G.mul_one a)
    ... = a * (b⁻¹ * b) : (G.φ a) # (Id.inv $ G.mul_left_inv b)
    ... = (a * b⁻¹) * b : Id.inv (G.mul_assoc a b⁻¹ b)

  @[hott] def cancel_right (a b : G.carrier) := calc
      a = a * e         : Id.inv (G.mul_one a)
    ... = a * (b * b⁻¹) : (G.φ a) # (Id.inv $ mul_right_inv b)
    ... = (a * b) * b⁻¹ : Id.inv (G.mul_assoc a b b⁻¹)

  @[hott] def rev_cancel_left (a b : G.carrier) := calc
      b = e * b         : Id.inv (G.one_mul b)
    ... = (a⁻¹ * a) * b : (λ c, G.φ c b) # (Id.inv $ G.mul_left_inv a)
    ... = a⁻¹ * (a * b) : G.mul_assoc a⁻¹ a b

  @[hott] def rev_cancel_right (a b : G.carrier) := calc
      b = e * b         : Id.inv (G.one_mul b)
    ... = (a * a⁻¹) * b : (λ c, G.φ c b) # (Id.inv $ mul_right_inv a)
    ... = a * (a⁻¹ * b) : G.mul_assoc a a⁻¹ b

  @[hott] def comm_impl_conj {x y : G.carrier} (p : x * y = y * x) : x = x ^ y := calc
      x = e * x         : Id.inv (G.one_mul x)
    ... = (y⁻¹ * y) * x : (* x) # (Id.inv $ G.mul_left_inv y)
    ... = y⁻¹ * (y * x) : G.mul_assoc y⁻¹ y x
    ... = y⁻¹ * (x * y) : G.φ y⁻¹ # (Id.inv p)
    ... = (y⁻¹ * x) * y : Id.inv (G.mul_assoc y⁻¹ x y)
    ... = x ^ y         : by reflexivity

  @[hott] def commutator (x y : G.carrier) := (x * y) * (x⁻¹ * y⁻¹)

  @[hott] def commutes {x y : G.carrier}
    (p : commutator x y = e) : x * y = y * x :=
  begin
    symmetry, transitivity, { symmetry, apply inv_inv },
    transitivity, apply Id.map, apply inv_explode,
    symmetry, apply eq_inv_of_mul_eq_one, exact p
  end

  @[hott] def commutator_over_inv (x y : G.carrier) :
    (commutator x y)⁻¹ = commutator y x :=
  begin
    transitivity, apply inv_explode,
    transitivity, apply Id.map, apply inv_explode,
    apply Id.map (* y⁻¹ * x⁻¹), transitivity, apply inv_explode,
    transitivity, apply Id.map, apply inv_inv,
    apply Id.map (* x), apply inv_inv
  end

  def ldiv (φ : G.subgroup) := λ x y, @left_div G x y ∈ φ
  def rdiv (φ : G.subgroup) := λ x y, x / y ∈ φ

  @[hott] def inv_x_mul_y_inv (x y : G.carrier) := calc
    (x⁻¹ * y)⁻¹ = y⁻¹ * x⁻¹⁻¹ : by apply inv_explode
            ... = y⁻¹ * x     : (G.φ y⁻¹) # (inv_inv x)

  @[hott] def x_mul_inv_y_inv (x y : G.carrier) := calc
    (x * y⁻¹)⁻¹ = y⁻¹⁻¹ * x⁻¹ : by apply inv_explode
            ... = y * x⁻¹     : (* x⁻¹) # (inv_inv y)

  @[hott] def div_by_unit (x : G.carrier) : x / e = x :=
  begin
    change _ * _ = _,
    transitivity, { apply Id.map, symmetry, apply unit_inv },
    apply G.mul_one
  end

  @[hott] def ldiv_by_unit (x : G.carrier) : left_div x e = x⁻¹ :=
  by apply G.mul_one

  @[hott] def chain_ldiv (x y z : G.carrier) := calc
          (left_div x y) * (left_div y z)
        = (x⁻¹ * y) * (y⁻¹ * z) : Id.refl
    ... = x⁻¹ * (y * (y⁻¹ * z)) : (G.mul_assoc x⁻¹ y (y⁻¹ * z))
    ... = x⁻¹ * ((y * y⁻¹) * z) : (G.φ x⁻¹) # (Id.inv $ G.mul_assoc y y⁻¹ z)
    ... = x⁻¹ * (e * z)         :
          begin
            apply map, apply map (* z),
            apply group.mul_right_inv
          end
    ... = left_div x z : (λ y, x⁻¹ * y) # (G.one_mul z)

  @[hott] def chain_rdiv (x y z : G.carrier) := calc
    (x / y) * (y / z) = (x * y⁻¹) * (y * z⁻¹) : Id.refl
                  ... = x * (y⁻¹ * (y * z⁻¹)) : (G.mul_assoc x y⁻¹ (y * z⁻¹))
                  ... = x * ((y⁻¹ * y) * z⁻¹) : (G.φ x) # (Id.inv $ G.mul_assoc y⁻¹ y z⁻¹)
                  ... = x * (e * z⁻¹)         :
                        begin
                          apply map, apply map (* z⁻¹),
                          apply G.mul_left_inv
                        end
                  ... = x / z : (λ y, x * y) # (G.one_mul z⁻¹)

  @[hott] def conjugate.idem (x : G.carrier) := calc
    conjugate x x = G.φ G.e x : (λ y, G.φ y x) # (G.mul_left_inv x)
              ... = x         : G.one_mul x

  @[hott] def conjugate.eq {x y : G.carrier}
    (p : conjugate x y = y) : x = y :=
  begin
    symmetry, apply eq_of_div_eq, fapply mul_cancel_right, exact y,
    transitivity, exact p, symmetry, apply G.one_mul
  end

  @[hott] def conjugate.comm {x y : G.carrier}
    (p : conjugate x y = x) : G.φ x y = G.φ y x :=
  begin
    fapply mul_cancel_left, exact G.ι y,
    transitivity, { symmetry, apply G.mul_assoc },
    transitivity, exact p, transitivity,
    { transitivity, symmetry, apply G.one_mul,
      apply Id.map (λ y, G.φ y x),
      symmetry, apply G.mul_left_inv y },
    apply G.mul_assoc
  end

  section
    variables {H K : pregroup}

    @[hott] def homo_unit (φ : H ⤳ K) : φ.fst H.e = K.e :=
    φ.snd.fst pregroup.arity.nullary ★

    @[hott] def homo_inv (φ : H ⤳ K) (x : H.carrier) :
      φ.fst (H.ι x) = K.ι (φ.fst x) :=
    φ.snd.fst pregroup.arity.unary (x, ★)

    @[hott] def homo_mul (φ : H ⤳ K) (x y : H.carrier) :
      φ.fst (H.φ x y) = K.φ (φ.fst x) (φ.fst y) :=
    φ.snd.fst pregroup.arity.binary (x, y, ★)
  end

  section
    variables {H : pregroup} [group H]
    local infix × : 70 := H.φ

    @[hott] def respects_saves_unit {φ : G.carrier → H.carrier}
      (p : Π a b, φ (a * b) = φ a × φ b) : φ G.e = H.e :=
    begin
      apply unit_of_sqr, calc
        φ G.e × φ G.e = φ (G.e * G.e) : Id.inv (p G.e G.e)
                  ... = φ G.e         : φ # (Id.inv unit_sqr)
    end

    @[hott] def mkhomo (φ : G.carrier → H.carrier)
      (p : Π a b, φ (a * b) = φ a × φ b) : G ⤳ H :=
    begin
      existsi φ, split; intros i v; induction i,
      { induction v, apply respects_saves_unit p },
      { induction v with x v, induction v, calc
        φ x⁻¹ = φ x⁻¹ × H.e               : Id.inv (H.mul_one (φ x⁻¹))
          ... = φ x⁻¹ × (φ x × H.ι (φ x)) : (λ y, φ x⁻¹ × y) # (Id.inv $ mul_right_inv (φ x))
          ... = φ x⁻¹ × φ x × H.ι (φ x)   : Id.inv (H.mul_assoc _ _ _)
          ... = φ (x⁻¹ * x) × H.ι (φ x)   : (× H.ι (φ x)) # (Id.inv (p x⁻¹ x))
          ... = φ G.e × H.ι (φ x)         : (λ y, φ y × H.ι (φ x)) # (G.mul_left_inv x)
          ... = H.e × H.ι (φ x)           : (× H.ι (φ x)) # (respects_saves_unit p)
          ... = H.ι (φ x)                 : H.one_mul (H.ι (φ x)) },
      { induction v with x v, induction v with y v,
        induction v, apply p }
    end

    @[hott] def mkiso (φ : G.carrier → H.carrier)
      (p : Π a b, φ (a * b) = φ a × φ b) (q : biinv φ) : G ≅ H :=
    ⟨φ, ((mkhomo φ p).snd, q)⟩

    @[hott] def iso_unit (φ : G ≅ H) : φ.fst G.e = H.e :=
    homo_unit φ.homo

    @[hott] def iso_inv (φ : G ≅ H) : Π x, φ.fst x⁻¹ = H.ι (φ.fst x) :=
    homo_inv φ.homo

    @[hott] def iso_mul (φ : G ≅ H) :
      Π x y, φ.fst (x * y) = φ.fst x × φ.fst y :=
    homo_mul φ.homo

    @[hott] def homo_respects_div (φ : G ⤳ H) (x y : G.carrier) :
      φ.fst (x / y) = right_div (φ.fst x) (φ.fst y) :=
    begin
      cases φ with φ p, calc
        φ (x / y) = φ x × φ y⁻¹     : homo_mul ⟨φ, p⟩ x y⁻¹
              ... = φ x × H.ι (φ y) : (λ y, φ x × y) # (homo_inv ⟨φ, p⟩ y)
    end

    @[hott] def homo.zero : G ⤳ H :=
    mkhomo (λ _, H.e) (λ _ _, Id.inv (H.one_mul H.e))
    instance : has_zero (G ⤳ H) := ⟨homo.zero⟩
  end

  @[hott] noncomputable def homo.set {G H : pregroup} : hset (G ⤳ H) :=
  λ _ _, algebra.homo.hset

  -- Of course, this can be done by induction
  @[hott] def homo.of_path {G H : pregroup} [group G] [group H]
    (φ : G.carrier = H.carrier) (p : G.φ =[λ G, G → G → G, φ] H.φ) : G ⤳ H :=
  begin
    fapply mkhomo, exact @transport _ (λ G, G) G.carrier H.carrier φ,
    intros a b, transitivity, apply Id.map, apply bimap,
    iterate 2 { symmetry, apply @equiv.transport_forward_and_back _ (λ G, G) _ _ φ },
    transitivity, symmetry, apply equiv.transport_over_operation_pointwise G.φ,
    iterate 2 { apply HITs.interval.happly }, exact p
  end

  @[hott] def iso.of_path {G H : pregroup} [group G] [group H]
    (φ : G.carrier = H.carrier) (p : G.φ =[λ G, G → G → G, φ] H.φ) : G ≅ H :=
  begin
    fapply iso.of_homo, apply homo.of_path φ p,
    split; existsi @transport _ (λ G, G) H.carrier G.carrier (Id.inv φ); intro x,
    { apply types.equiv.transport_forward_and_back },
    { apply @types.equiv.transport_back_and_forward _ (λ G, G) _ _ φ },
  end

  @[hott] noncomputable def iso.ua {G H : pregroup} : G ≅ H → G = H :=
  @Alg.ua.{0 0 0} pregroup.arity ⊥ pregroup.signature G H

  -- This statement in fact says that two groups are equal
  -- if their multiplication tables are equal
  @[hott] noncomputable def table {G H : pregroup} [group G] [group H]
    (φ : G.carrier = H.carrier) (p : G.φ =[λ G, G → G → G, φ] H.φ) : G = H :=
  iso.ua (iso.of_path φ p)

  @[hott] def Z₁.mul : 𝟏 → 𝟏 → 𝟏 := λ _ _, ★
  @[hott] def Z₁.inv : 𝟏 → 𝟏     := λ _, ★

  @[hott] instance Z₁.has_mul : has_mul 𝟏 := ⟨Z₁.mul⟩
  @[hott] instance Z₁.has_inv : has_inv 𝟏 := ⟨Z₁.inv⟩
  @[hott] instance Z₁.has_one : has_one 𝟏 := ⟨★⟩

  @[hott] def Z₁ : pregroup :=
  @pregroup.intro 𝟏 (λ _ _, unit_is_set) Z₁.mul Z₁.inv ★

  @[hott] instance Z₁.semigroup : semigroup Z₁.magma :=
  ⟨begin intros, reflexivity end⟩

  @[hott] instance Z₁.monoid : monoid Z₁.premonoid :=
  ⟨Z₁.semigroup,
    begin intro x, induction x, reflexivity end,
    begin intro x, induction x, reflexivity end⟩

  @[hott] instance Z₁.group : group Z₁ :=
  ⟨Z₁.monoid, begin intros x, reflexivity end⟩

  @[hott] instance Z₁.abelian : abelian Z₁ :=
  ⟨begin intros x y, reflexivity end⟩

  def Z₂.carrier := bool
  def Z₂.mul     := bxor
  def Z₂.inv     := @ground_zero.proto.idfun Z₂.carrier

  @[hott] instance Z₂.has_one : has_one Z₂.carrier := ⟨ff⟩
  @[hott] instance Z₂.has_inv : has_inv Z₂.carrier := ⟨Z₂.inv⟩
  @[hott] instance Z₂.has_mul : has_mul Z₂.carrier := ⟨Z₂.mul⟩

  @[hott] def Z₂.set : hset Z₂.carrier :=
  begin
    apply ground_zero.structures.Hedberg,
    intros x y, induction x; induction y; try { apply sum.inl, refl },
    repeat { apply sum.inr, intro p, apply ff_neq_tt },
    exact p, exact Id.inv p
  end

  @[hott] def Z₂ : pregroup :=
  @pregroup.intro Z₂.carrier (λ _ _, Z₂.set) Z₂.mul Z₂.inv ff

  @[hott] instance Z₂.semigroup : semigroup Z₂.magma :=
  ⟨begin intros a b c, induction a; induction b; induction c; trivial end⟩

  @[hott] instance Z₂.monoid : monoid Z₂.premonoid :=
  ⟨Z₂.semigroup,
    begin intro a; induction a; trivial end,
    begin intro a; induction a; trivial end⟩

  @[hott] instance Z₂.group : group Z₂ :=
  ⟨Z₂.monoid, begin intro a, induction a; trivial end⟩

  section
    variable {H : pregroup}
    @[hott] def op.mul := λ x y, H.φ y x
    @[hott] def op.inv := H.ι
    @[hott] def op.one := H.e
  end

  @[hott] def op (G : pregroup) : pregroup :=
  @pregroup.intro G.carrier (λ _ _, G.hset) op.mul op.inv op.one
  postfix `ᵒᵖ`:2000 := op

  @[hott] instance op.semigroup : semigroup Gᵒᵖ.magma :=
  ⟨λ a b c, Id.inv (G.mul_assoc c b a)⟩

  @[hott] instance op.monoid : monoid Gᵒᵖ.premonoid :=
  ⟨op.semigroup, G.mul_one, G.one_mul⟩

  @[hott] instance op.group : group Gᵒᵖ :=
  ⟨op.monoid, λ x, mul_right_inv x⟩

  @[hott] def op.univ : G ⤳ Gᵒᵖ :=
  mkhomo G.ι inv_explode

  @[hott] def op.iso : G ≅ Gᵒᵖ :=
  begin
    fapply mkiso, exact G.ι, apply inv_explode,
    split; existsi G.ι; intro x; apply inv_inv
  end
end group

end ground_zero.algebra