import ground_zero.algebra.group
open ground_zero.algebra.group (factor_left)
open ground_zero.types.equiv (transport)
open ground_zero.types.Id (map)
open ground_zero.structures
open ground_zero.types
open ground_zero

hott theory

namespace ground_zero.algebra
universes u v

namespace prering
  inductive arity : Type
  | nullary | unary | add | mul
  open arity

  def signature : arity + ⊥ → ℕ
  | (sum.inl nullary) := 0
  | (sum.inl unary)   := 1
  | (sum.inl add)     := 2
  | (sum.inl mul)     := 2
end prering

def prering : Type (u + 1) :=
Alg.{0 0 u 0} prering.signature

namespace overring
  def signature : prering.arity + 𝟏 → ℕ
  | (sum.inl v) := prering.signature (sum.inl v)
  | (sum.inr _) := 2
end overring

def overring : Type (max u v + 1) :=
Alg.{0 0 u v} overring.signature

namespace prering
  @[hott] def intro {α : Type u} (H : hset α)
    (φ ψ : α → α → α) (ι : α → α) (e : α) : prering :=
  begin
    existsi zeroeqv (λ _ _, H), split; intro i; induction i,
    exact (λ _, e), exact (λ ⟨a, _⟩, ι a),
    exact (λ ⟨a, b, _⟩, φ a b), exact (λ ⟨a, b, _⟩, ψ a b)
  end

  def zero (T : prering) : T.carrier :=
  T.op arity.nullary ★

  def neg (T : prering) : T.carrier → T.carrier :=
  λ x, T.op arity.unary (x, ★)

  def φ (T : prering) : T.carrier → T.carrier → T.carrier :=
  λ x y, T.op arity.add (x, y, ★)

  def ψ (T : prering) : T.carrier → T.carrier → T.carrier :=
  λ x y, T.op arity.mul (x, y, ★)

  @[hott] def pregroup (T : prering) : pregroup :=
  pregroup.intro (λ _ _, T.hset) T.φ T.neg T.zero

  abbreviation additive := pregroup
end prering

namespace overring
  @[hott] def intro {α : Type u} (H : hset α) (φ ψ : α → α → α)
    (ι : α → α) (e : α) (ρ : α → α → Ω) : overring :=
  begin
    existsi zeroeqv (λ _ _, H), split; intro i; induction i,
    exact (λ _, e), exact (λ ⟨a, _⟩, ι a),
    exact (λ ⟨a, b, _⟩, φ a b),
    exact (λ ⟨a, b, _⟩, ψ a b),
    exact (λ ⟨a, b, _⟩, ρ a b)
  end

  def rel (T : overring) (x y : T.carrier) : Ω := T.rel ★ (x, y, ★)
  def ρ (T : overring) (x y : T.carrier) := (T.rel x y).1

  @[hott] def τ (T : overring) : prering :=
  ⟨T.1, (T.2.1, by intro i; induction i)⟩
end overring

class ring (T : prering) :=
(abgroup       : abelian T.pregroup)
(distrib_left  : Π a b c, T.ψ a (T.φ b c) = T.φ (T.ψ a b) (T.ψ a c))
(distrib_right : Π a b c, T.ψ (T.φ a b) c = T.φ (T.ψ a c) (T.ψ b c))

postfix `⁺`:1034 := prering.pregroup
instance abring (T : prering) [ring T] : abelian T⁺ := ring.abgroup

section
  variable (T : prering)
  def prering.sub (x y : T.carrier) := T.φ x (T.neg y)

  def prering.isproper (x : T.carrier) := T.pregroup.isproper x
  def prering.proper := T.pregroup.proper

  def prering.proper_hset : hset T.proper :=
  begin
    apply hset_respects_sigma,
    intros a b, apply T.pregroup.hset,
    intro x, apply prop_is_set, apply not_is_prop
  end

  instance : has_add T.carrier := ⟨T.φ⟩
  instance : has_sub T.carrier := ⟨T.sub⟩
  instance : has_neg T.carrier := ⟨T.neg⟩

  instance : has_mul T.carrier := ⟨T.ψ⟩

  instance : has_zero T.carrier := ⟨T.zero⟩
end

section
  variable (T : overring)
  instance : has_add T.carrier := ⟨T.τ.φ⟩
  instance : has_sub T.carrier := ⟨T.τ.sub⟩
  instance : has_neg T.carrier := ⟨T.τ.neg⟩

  instance : has_mul T.carrier := ⟨T.τ.ψ⟩

  instance : has_zero T.carrier := ⟨T.τ.zero⟩

  infix <= := overring.ρ _
  infix ≤  := overring.ρ _
end

namespace prering
  variables (T : prering) [ring T]

  @[hott] def add_assoc (a b c : T.carrier) : (a + b) + c = a + (b + c) :=
  T.pregroup.mul_assoc a b c

  @[hott] def zero_add (a : T.carrier) : 0 + a = a :=
  T.pregroup.one_mul a

  @[hott] def add_zero (a : T.carrier) : a + 0 = a :=
  T.pregroup.mul_one a

  @[hott] def add_comm (a b : T.carrier) : a + b = b + a :=
  T.pregroup.mul_comm a b

  @[hott] def add_left_neg (a : T.carrier) : (-a) + a = 0 :=
  T.pregroup.mul_left_inv a

  @[hott] def distrib_left (a b c : T.carrier) : a * (b + c) = a * b + a * c :=
  ring.distrib_left a b c

  @[hott] def distrib_right (a b c : T.carrier) : (a + b) * c = a * c + b * c :=
  ring.distrib_right a b c
end prering

section
  variables {T : prering} [ring T]

  @[hott] def ring.mul_zero (a : T.carrier) : a * 0 = 0 :=
  begin
    apply @group.unit_of_sqr T⁺,
    transitivity, { symmetry, apply ring.distrib_left },
    apply map (T.ψ a), apply T.zero_add
  end

  @[hott] def ring.zero_mul (a : T.carrier) : 0 * a = 0 :=
  begin
    apply @group.unit_of_sqr T⁺, transitivity,
    { symmetry, apply T.distrib_right },
    apply map (* a), apply T.add_zero
  end

  @[hott] def ring.mul_neg (a b : T.carrier) : a * (-b) = -(a * b) :=
  begin
    apply @group.eq_inv_of_mul_eq_one T⁺, transitivity,
    { symmetry, apply T.distrib_left }, transitivity,
    { apply map (T.ψ a), apply T.add_left_neg },
    apply ring.mul_zero
  end

  @[hott] def ring.neg_mul (a b : T.carrier) : (-a) * b = -(a * b) :=
  begin
    apply @group.eq_inv_of_mul_eq_one T⁺, transitivity,
    { symmetry, apply T.distrib_right }, transitivity,
    { apply map (* b), apply T.add_left_neg },
    apply ring.zero_mul
  end

  @[hott] def ring.sub_distrib_left (a b c : T.carrier) := calc
    a * (b - c) = a * b + a * (-c) : T.distrib_left a b (T.neg c)
            ... = a * b - a * c    : (T.φ (T.ψ a b)) # (ring.mul_neg a c)

  @[hott] def ring.sub_distrib_right (a b c : T.carrier) := calc
    (a - b) * c = a * c + (-b) * c : T.distrib_right a (T.neg b) c
            ... = a * c - b * c    : (T.φ (T.ψ a c)) # (ring.neg_mul b c)
end

class ring.assoc (T : prering) :=
(mul_assoc : Π a b c, T.ψ (T.ψ a b) c = T.ψ a (T.ψ b c))

class ring.comm (T : prering) :=
(mul_comm : Π a b, T.ψ a b = T.ψ b a)

class ring.monoid (T : prering) extends has_one T.carrier :=
(one_mul : Π a, T.ψ one a = a)
(mul_one : Π a, T.ψ a one = a)

class ring.divisible (T : prering) extends has_inv T.carrier, ring.monoid T :=
(zero_inv     : inv 0 = 0)
(mul_left_inv : Π (x : T.carrier), T.isproper x → inv x * x = 1)

class field (T : prering) extends ring T, ring.assoc T, ring.divisible T, ring.comm T :=
(nontrivial : T.isproper 1)

@[hott] def field.proper_mul {T : prering} [field T] {a b : T.carrier} :
  T.isproper a → T.isproper b → T.isproper (a * b) :=
begin
  intros p q r, apply @field.nontrivial T _,
  transitivity, { symmetry, apply ring.divisible.mul_left_inv b q },
  transitivity, { apply map (* b), symmetry, apply ring.monoid.mul_one },
  transitivity, apply ring.assoc.mul_assoc,
  transitivity, apply map (λ y, b⁻¹ * (y * b)),
  { symmetry, apply ring.divisible.mul_left_inv a p },
  transitivity, apply map (T.ψ _), apply ring.assoc.mul_assoc,
  transitivity, { symmetry, apply ring.assoc.mul_assoc },
  transitivity, apply map, exact r, apply ring.mul_zero
end

@[hott] def field.prop_inv {T : prering} [field T] {a : T.carrier} :
  T.isproper a → T.isproper a⁻¹ :=
begin
  intros p q, apply @field.nontrivial T _,
  transitivity, { symmetry, apply ring.divisible.mul_left_inv a p },
  transitivity, apply map (* a), exact q, apply ring.zero_mul
end

@[hott] def field.mul (T : prering) [field T] :
  T.proper → T.proper → T.proper :=
λ ⟨a, p⟩ ⟨b, q⟩, ⟨T.ψ a b, field.proper_mul p q⟩

@[hott] def field.inv (T : prering) [field T] : T.proper → T.proper :=
λ ⟨a, p⟩, ⟨@has_inv.inv T.carrier _ a, field.prop_inv p⟩

@[hott] def ring.proper_eq {T : prering.{u}}
  {x y : T.proper} (p : x.fst = y.fst) : x = y :=
begin fapply sigma.prod, exact p, apply not_is_prop end

@[hott] def multiplicative (T : prering) [field T] : pregroup :=
pregroup.intro (λ _ _, T.proper_hset) (field.mul T) (field.inv T) ⟨1, field.nontrivial⟩
postfix `ˣ`:1034 := multiplicative

section
  variables (T : prering) [field T]

  @[hott] instance multiplicative.semigroup : semigroup Tˣ.magma :=
  ⟨λ ⟨a, p⟩ ⟨b, q⟩ ⟨c, r⟩, begin
    fapply @ring.proper_eq T,
    apply @ring.assoc.mul_assoc T
  end⟩

  @[hott] instance multiplicative.monoid : monoid Tˣ.premonoid :=
  ⟨multiplicative.semigroup T,
  λ ⟨a, p⟩, ring.proper_eq (ring.monoid.one_mul a),
  λ ⟨a, p⟩, ring.proper_eq (ring.monoid.mul_one a)⟩

  @[hott] instance multiplicative.group : group Tˣ :=
  ⟨multiplicative.monoid T, λ ⟨a, p⟩, ring.proper_eq (ring.divisible.mul_left_inv a p)⟩
end

-- voilà, no need to repeat a bunch of lemmas
@[hott] def field.mul_right_inv (T : prering) [field T] {x : T.carrier}
  (p : T.isproper x) : x * x⁻¹ = 1 :=
sigma.fst # (@group.mul_right_inv Tˣ _ ⟨x, p⟩)

class lid (T : prering) (φ : T⁺.subgroup) :=
(ideal : Π r i, i ∈ φ → T.ψ r i ∈ φ.set)

class rid (T : prering) (φ : T⁺.subgroup) :=
(ideal : Π i r, i ∈ φ → T.ψ i r ∈ φ.set)

class ideal (T : prering) (φ : T⁺.subgroup) :=
(left  : Π r i, i ∈ φ → T.ψ r i ∈ φ.set)
(right : Π i r, i ∈ φ → T.ψ i r ∈ φ.set)

instance ideal.auto (T : prering) (φ : T⁺.subgroup)
  [lid T φ] [rid T φ] : ideal T φ :=
⟨lid.ideal, rid.ideal⟩

namespace ring
  variables (T : prering) [ring T] (φ : T⁺.subgroup) [ideal T φ]

  @[hott] instance normal : T⁺ ⊵ φ :=
  group.abelian_subgroup_is_normal T⁺ φ

  noncomputable def factor.mul : factor_left T⁺ φ → factor_left T⁺ φ → factor_left T⁺ φ :=
  begin
    fapply HITs.quotient.lift₂,
    { intros a b, apply HITs.quotient.elem, exact T.ψ a b },
    { apply HITs.quotient.set },
    { intros a₁ a₂ b₁ b₂ p q,
      apply HITs.quotient.sound,
      apply transport (∈ φ),
      { let φ' := @pregroup.left_div T⁺,
        change T.φ (φ' (T.ψ a₁ a₂) (T.ψ a₁ b₂)) (φ' (T.ψ a₁ b₂) (T.ψ b₁ b₂)) = _,
        transitivity, apply T⁺.mul_assoc,
        transitivity, apply Id.map (T.φ _),
        transitivity, symmetry, apply T⁺.mul_assoc,
        apply Id.map (λ z, T.φ z (T.ψ b₁ b₂)),
        apply group.mul_right_inv,
        apply Id.map, apply T.zero_add },
      apply φ.mul,
      { apply transport (∈ φ),
        transitivity, apply T.distrib_left a₁ (T.neg a₂) b₂,
        apply Id.map (λ z, T.φ z (T.ψ a₁ b₂)),
        apply ring.mul_neg, apply ideal.left, exact q },
      { apply transport (∈ φ),
        transitivity, apply T.distrib_right (T.neg a₁) b₁ b₂,
        apply Id.map (λ z, T.φ z (T.ψ b₁ b₂)),
        apply ring.neg_mul, apply ideal.right, exact p } }
  end

  meta def πprop :=
  `[ repeat { intros, apply structures.pi_prop <|> apply HITs.quotient.set } ]

  meta def quotΩind :=
  `[ intro x, fapply HITs.quotient.ind_prop _ _ x; clear x ]

  @[hott] noncomputable def factor : prering :=
  prering.intro (λ _ _, (T⁺\φ).hset) (T⁺\φ).φ (factor.mul T φ) (T⁺\φ).ι (T⁺\φ).e

  @[hott] noncomputable instance factor.abgroup : abelian (T⁺\φ) :=
  ⟨begin
    iterate 2 { quotΩind, intros },
    apply Id.map HITs.quotient.elem,
    apply T.add_comm, repeat { πprop }
  end⟩

  @[hott] noncomputable instance factor.ring : ring (factor T φ) :=
  ⟨factor.abgroup T φ, begin
    iterate 3 { quotΩind, intros },
    apply Id.map HITs.quotient.elem,
    apply ring.distrib_left,
    repeat { πprop }
  end, begin
    iterate 3 { quotΩind, intros },
    apply Id.map HITs.quotient.elem,
    apply ring.distrib_right,
    repeat { πprop }
  end⟩

  infix \ := factor
end ring

end ground_zero.algebra