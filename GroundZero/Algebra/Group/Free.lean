import GroundZero.Algebra.Group.Basic
open GroundZero.Types.Equiv (biinv transport)
open GroundZero.Types.Id (map)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero

/-
  Free group.
  * https://en.wikipedia.org/wiki/Free_group
-/

namespace GroundZero.Algebra
universe u v w

namespace Group
  inductive Exp (α : Type u)
  | unit : Exp α
  | elem : α → Exp α
  | mul  : Exp α → Exp α → Exp α
  | inv  : Exp α → Exp α

  namespace Exp
    variable {α : Type u} (G : Group) (f : α → G.carrier)

    hott def eval : Exp α → G.carrier
    | unit    => G.e
    | elem x  => f x
    | mul x y => G.φ (eval x) (eval y)
    | inv x   => G.ι (eval x)
  end Exp

  private structure F.aux (α : Type u) :=
  (val : Exp α)

  def F.carrier (α : Type u) := F.aux α

  namespace F
    attribute [nothott] F.aux.recOn F.aux.rec aux.val

    variable {ε : Type u}
    hott def unit : F.carrier ε := ⟨Exp.unit⟩
    hott def elem : ε → F.carrier ε := λ x, ⟨Exp.elem x⟩

    @[hottAxiom] def mul (x y : F.carrier ε) : F.carrier ε := ⟨Exp.mul x.val y.val⟩
    @[hottAxiom] def inv (x : F.carrier ε)   : F.carrier ε := ⟨Exp.inv x.val⟩

    instance : Mul (F.carrier ε) := ⟨mul⟩
    instance : OfNat (F.carrier ε) (Nat.succ Nat.zero) := ⟨unit⟩

    axiom mulAssoc (a b c : F.carrier ε) : mul (mul a b) c = mul a (mul b c)
    axiom oneMul       (a : F.carrier ε) : mul unit a = a
    axiom mulOne       (a : F.carrier ε) : mul a unit = a
    axiom mulLeftInv   (a : F.carrier ε) : mul (inv a) a = unit

    axiom ens : Structures.hset (F.carrier ε)

    @[hottAxiom] def rec (G : Group) (f : ε → G.carrier) (x : F.carrier ε) :=
    Exp.eval G f x.val

    @[hottAxiom, eliminator] noncomputable def ind
      {π : F.carrier ε → Type v}
      (setπ : Π x, Structures.hset (π x))
      (u : π unit) (η : Π {x}, π (elem x))
      (m : Π {x y}, π x → π y → π (mul x y))
      (i : Π {x}, π x → π (inv x))
      (mulAssoc : Π {x y z : F.carrier ε} (a : π x) (b : π y) (c : π z),
        m (m a b) c =[mulAssoc x y z] m a (m b c))
      (oneMul : Π {x : F.carrier ε} (a : π x), m u a =[oneMul x] a)
      (mulOne : Π {x : F.carrier ε} (a : π x), m a u =[mulOne x] a)
      (mulLeftInv : Π {x : F.carrier ε} (a : π x),
        m (i a) a =[mulLeftInv x] u) : Π x, π x :=
    begin
      intro ⟨x⟩; induction x; exact u; apply η;
      apply m; assumption; assumption;
      apply i; assumption
    end

  end F

  noncomputable def F (ε : Type u) : Group :=
  @Group.intro (F.carrier ε) F.ens F.mul F.inv F.unit F.mulAssoc F.oneMul F.mulOne F.mulLeftInv

  attribute [irreducible] F.carrier

  namespace F
    variable {G : Group} {ε : Type u}

    local infixl:70 (priority := high) " * " => G.φ
    local postfix:max (priority := high) "⁻¹" => G.ι
    local notation "e" => G.e

    hott def recMul (f : ε → G.carrier) (x y : F.carrier ε) :
      rec G f (mul x y) = rec G f x * rec G f y :=
    by reflexivity

    hott def recInv (f : ε → G.carrier) (x : F.carrier ε) :
      rec G f (inv x) = (rec G f x)⁻¹ :=
    by reflexivity

    hott def recOne (f : ε → G.carrier) : rec G f unit = e :=
    by reflexivity

    noncomputable hott def homomorphism (f : ε → G.carrier) : Hom (F ε) G :=
    mkhomo (rec G f) (recMul f)

    noncomputable def recβrule₁ {a b c : F.carrier ε} (f : ε → G.carrier) :
      Id.map (rec G f) (mulAssoc a b c) =
        G.mulAssoc (rec G f a) (rec G f b) (rec G f c) :=
    by apply G.hset

    noncomputable def recβrule₂ {a : F.carrier ε} (f : ε → G.carrier) :
      Id.map (rec G f) (oneMul a) = G.oneMul (rec G f a) :=
    by apply G.hset

    noncomputable def recβrule₃ {a : F.carrier ε} (f : ε → G.carrier) :
      Id.map (rec G f) (mulOne a) = G.mulOne (rec G f a) :=
    by apply G.hset

    noncomputable def recβrule₄ {a : F.carrier ε} (f : ε → G.carrier) :
      Id.map (rec G f) (mulLeftInv a) = G.mulLeftInv (rec G f a) :=
    by apply G.hset

    noncomputable hott def ind_prop {π : F.carrier ε → Type v}
      (propπ : Π x, prop (π x))
      (u : π unit) (η : Π {x}, π (elem x))
      (m : Π {x y}, π x → π y → π (mul x y))
      (i : Π {x}, π x → π (inv x)) : Π x, π x :=
    begin
      fapply ind;
      { intro; apply propIsSet; apply propπ };
      { exact u };
      { intro x; apply η };
      { intros x y u v; apply m u v };
      { intros x u; apply i u };
      repeat { intros; apply propπ }
    end
  end F
end Group

end GroundZero.Algebra