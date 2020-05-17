import ground_zero.algebra.group
open ground_zero.structures (groupoid)
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

  axiom indβrule {π : K1 α → Type v}
    (baseπ : π base) (loopπ : Π (x : α), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : α),
      loopπ (x * y) =[λ p, baseπ =[p] baseπ, loop.mul x y]
        loopπ x ⬝' loopπ y)
    (groupoidπ : Π x, groupoid (π x)) :
    Π x, equiv.apd (ind baseπ loopπ mulπ groupoidπ) (loop x) = loopπ x

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
end K1

end ground_zero.algebra