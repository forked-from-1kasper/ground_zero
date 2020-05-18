import ground_zero.algebra.group ground_zero.theorems.prop
open ground_zero.theorems.functions ground_zero.theorems.prop
open ground_zero.structures
open ground_zero.types.eq (dotted)
open ground_zero.types

namespace ground_zero.algebra
universes u v

hott theory

private structure K1.aux :=
(val : 𝟏)

def K1 (α : Type u) [group α] := K1.aux

namespace K1
  variables {α : Type u} [group α]

  attribute [nothott] K1.aux.rec_on K1.aux.rec aux.val

  @[hott] def base : K1 α := ⟨★⟩

  axiom grpd     : groupoid (K1 α)
  axiom loop     : α → (base = base :> K1 α)
  axiom loop.mul : Π (x y : α), loop (x * y) = loop x ⬝ loop y

  @[safe] def ind {π : K1 α → Type v}
    (baseπ : π base) (loopπ : Π (x : α), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : α),
      loopπ (x * y) =[λ p, baseπ =[p] baseπ, loop.mul x y]
        loopπ x ⬝' loopπ y)
    (groupoidπ : Π x, groupoid (π x)) : Π x, π x
  | ⟨★⟩ := baseπ

  @[safe] def rec {π : Type v} (baseπ : π)
    (loopπ : α → baseπ = baseπ)
    (mulπ : Π x y, loopπ (x * y) = loopπ x ⬝ loopπ y)
    (groupoidπ : groupoid π) : K1 α → π
  | ⟨★⟩ := baseπ

  axiom indβrule {π : K1 α → Type v}
    (baseπ : π base) (loopπ : Π (x : α), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : α),
      loopπ (x * y) =[λ p, baseπ =[p] baseπ, loop.mul x y]
        loopπ x ⬝' loopπ y)
    (groupoidπ : Π x, groupoid (π x)) :
    Π x, equiv.apd (ind baseπ loopπ mulπ groupoidπ) (loop x) = loopπ x

  axiom recβrule {π : Type v} (baseπ : π) (loopπ : α → baseπ = baseπ)
    (mulπ : Π x y, loopπ (x * y) = loopπ x ⬝ loopπ y) (groupoidπ : groupoid π) :
    Π x, (rec baseπ loopπ mulπ @groupoidπ) # (loop x) = loopπ x

  attribute [irreducible] K1

  instance : dotted (K1 α) := ⟨base⟩

  instance : has_mul (Ω¹(K1 α)) := ⟨λ p q, p ⬝ q⟩
  instance : has_one (Ω¹(K1 α)) := ⟨idp base⟩
  instance : has_inv (Ω¹(K1 α)) := ⟨eq.inv⟩

  noncomputable instance : magma (Ω¹(K1 α)) :=
  begin split, apply grpd end

  noncomputable instance : semigroup (Ω¹(K1 α)) :=
  begin split, intros p q r, symmetry, apply eq.assoc end

  noncomputable instance : monoid (Ω¹(K1 α)) := begin
    split; intro p, apply eq.refl_left, apply eq.refl_right
  end

  noncomputable instance : group (Ω¹(K1 α)) :=
  begin split, intro p, apply eq.inv_comp end

  noncomputable def homomorphism : α ⤳ Ω¹(K1 α) :=
  ⟨loop, loop.mul⟩

  noncomputable def loop.one : loop 1 = idp base :> Ω¹(K1 α) :=
  by apply group.homo_saves_unit homomorphism

  noncomputable def loop.inv (p : Ω¹(K1 α)) : loop p⁻¹ = (loop p)⁻¹ :=
  by apply group.homo_respects_inv homomorphism

  @[hott] noncomputable def ntype_is_succ_n_type (n : ℕ₋₂) :
    is-(hlevel.succ n)-type (n-Type) := begin
    intros x y,
    induction x with X p, induction y with Y p',
    apply ntype_respects_equiv,
    symmetry, apply sigma.sigma_path,
    { fapply ntype_respects_sigma,
      { apply ntype_respects_equiv,
        exact ground_zero.ua.univalence X Y,
        induction n with n ih,
        { existsi contr_type_equiv p p',
          intro e, fapply sigma.prod,
          { apply ground_zero.theorems.funext,
            intro x, apply contr_impl_prop, exact p' },
          { apply biinv_prop } },
        { fapply ntype_over_embedding equiv.forward,
          { apply prop_sigma_embedding, apply biinv_prop },
          { apply pi_respects_ntype (hlevel.succ n),
            intro x, apply p' } } },
      { intros q, apply ground_zero.structures.prop_is_ntype,
        apply ntype_is_prop } }
  end
end K1

end ground_zero.algebra