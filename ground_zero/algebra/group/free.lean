import ground_zero.algebra.group.basic
open ground_zero.types.equiv (biinv transport)
open ground_zero.types.Id (map)
open ground_zero.structures
open ground_zero.types
open ground_zero.proto
open ground_zero

/-
  Free group.
  * https://en.wikipedia.org/wiki/Free_group
-/

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group

  inductive exp (α : Type u)
  | unit {} : exp
  | elem {} : α → exp
  | mul  {} : exp → exp → exp
  | inv  {} : exp → exp

  namespace exp
    @[hott] def eval {α : Type u} (G : pregroup)
      (f : α → G.carrier) : exp α → G.carrier
    | unit      := G.e
    | (elem x)  := f x
    | (mul x y) := G.φ (eval x) (eval y)
    | (inv x)   := G.ι (eval x)
  end exp

  private structure F.aux (α : Type u) :=
  (val : exp α)

  def F.carrier (α : Type u) := F.aux α

  namespace F
    variables {ε : Type u}
    attribute [nothott] F.aux.rec_on F.aux.rec aux.val

    @[hott] def unit : F.carrier ε := ⟨exp.unit⟩
    @[hott] def elem : ε → F.carrier ε := λ x, ⟨exp.elem x⟩

    @[safe] def mul (x y : F.carrier ε) : F.carrier ε := ⟨exp.mul x.val y.val⟩
    @[safe] def inv (x : F.carrier ε)   : F.carrier ε := ⟨exp.inv x.val⟩

    instance : has_one (F.carrier ε) := ⟨unit⟩
    instance : has_mul (F.carrier ε) := ⟨mul⟩
    instance : has_inv (F.carrier ε) := ⟨inv⟩

    local infix ` ∗ `:50 := has_mul.mul
    axiom mul_assoc (a b c : F.carrier ε) : mul (mul a b) c = mul a (mul b c)
    axiom one_mul       (a : F.carrier ε) : mul unit a = a
    axiom mul_one       (a : F.carrier ε) : mul a unit = a
    axiom mul_left_inv  (a : F.carrier ε) : mul (inv a) a = unit

    axiom ens : hset (F.carrier ε)

    @[safe] def rec (G : pregroup) [group G] (f : ε → G.carrier) (x : F.carrier ε) :=
    exp.eval G f x.val

    @[safe] def ind {π : F.carrier ε → Type v}
      (setπ : Π x, hset (π x))
      (u : π unit) (η : Π {x}, π (elem x))
      (m : Π {x y}, π x → π y → π (mul x y))
      (i : Π {x}, π x → π (inv x))
      (mul_assoc : Π {x y z : F.carrier ε} (a : π x) (b : π y) (c : π z),
        m (m a b) c =[mul_assoc x y z] m a (m b c))
      (one_mul : Π {x : F.carrier ε} (a : π x), m u a =[one_mul x] a)
      (mul_one : Π {x : F.carrier ε} (a : π x), m a u =[mul_one x] a)
      (mul_left_inv : Π {x : F.carrier ε} (a : π x),
        m (i a) a =[mul_left_inv x] u) : Π x, π x :=
    begin
      intro x, cases x, induction x with x x y u v x u,
      { exact u }, { apply η }, { apply m u v }, { apply i u }
    end

    attribute [irreducible] F.carrier
  end F

  noncomputable def F (ε : Type u) : pregroup :=
  @pregroup.intro (F.carrier ε) (λ _ _, F.ens) F.mul F.inv F.unit

  section
    variable (ε : Type u)
    noncomputable instance F.semigroup : semigroup (F ε).magma :=
    ⟨F.mul_assoc⟩

    noncomputable instance F.monoid : monoid (F ε).premonoid :=
    ⟨F.semigroup ε, F.one_mul, F.mul_one⟩

    noncomputable instance F.group : group (F ε) :=
    ⟨F.monoid ε, F.mul_left_inv⟩
  end

  namespace F
    variables {G : pregroup} [group G] {ε : Type u}

    local infix ` * `  := G.φ
    local notation `e` := G.e
    local postfix ⁻¹   := G.ι

    @[hott] def rec_mul (f : ε → G.carrier) (x y : F.carrier ε) :
      rec G f (mul x y) = rec G f x * rec G f y :=
    by reflexivity

    @[hott] def rec_inv (f : ε → G.carrier) (x : F.carrier ε) :
      rec G f (inv x) = (rec G f x)⁻¹ :=
    by reflexivity

    @[hott] def rec_one (f : ε → G.carrier) : rec G f unit = e :=
    by reflexivity

    @[hott] noncomputable def homomorphism (f : ε → G.carrier) : F ε ⤳ G :=
    mkhomo (rec G f) (rec_mul f)

    noncomputable def recβrule₁ {a b c : F.carrier ε} (f : ε → G.carrier) :
      rec G f # (mul_assoc a b c) =
        G.mul_assoc (rec G f a) (rec G f b) (rec G f c) :=
    by apply G.hset
    noncomputable def recβrule₂ {a : F.carrier ε} (f : ε → G.carrier) :
      rec G f # (one_mul a) = G.one_mul (rec G f a) :=
    by apply G.hset
    noncomputable def recβrule₃ {a : F.carrier ε} (f : ε → G.carrier) :
      rec G f # (mul_one a) = G.mul_one (rec G f a) :=
    by apply G.hset
    noncomputable def recβrule₄ {a : F.carrier ε} (f : ε → G.carrier) :
      rec G f # (mul_left_inv a) = G.mul_left_inv (rec G f a) :=
    by apply G.hset

    @[hott] noncomputable def ind_prop {π : F.carrier ε → Type v}
      (propπ : Π x, prop (π x))
      (u : π unit) (η : Π {x}, π (elem x))
      (m : Π {x y}, π x → π y → π (mul x y))
      (i : Π {x}, π x → π (inv x)) : Π x, π x :=
    begin
      fapply ind, { intro x, apply prop_is_set, apply propπ },
      { exact u },
      { intro x, apply η },
      { intros x y u v, apply m u v },
      { intros x u, apply i u },
      repeat { intros, apply propπ }
    end
  end F
end group

end ground_zero.algebra