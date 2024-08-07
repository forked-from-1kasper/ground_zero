import GroundZero.Algebra.Basic
import GroundZero.HITs.Trunc

open GroundZero GroundZero.Types
open GroundZero.Types.Id (ap)

namespace GroundZero.Algebra

universe u v

hott def Monoid := Σ (M : Magma), M.isAssociative × M.isUnital

namespace Monoid
  variable (M : Monoid)

  hott def carrier := M.1.carrier
  hott def subset  := M.1.subset
  hott def hset    := M.1.hset
  hott def magma   := M.1

  hott def φ := M.1.φ
  hott def e := M.2.2.1

  hott def mulAssoc : Π a b c, M.φ (M.φ a b) c = M.φ a (M.φ b c) := M.2.1

  hott def oneMul (a : M.carrier) : M.φ M.e a = a := (M.2.2.2 a).1
  hott def mulOne (a : M.carrier) : M.φ a M.e = a := (M.2.2.2 a).2

  hott def isCommutative := M.1.isCommutative

  hott def Hom (G H : Monoid) := Algebra.Hom G.1 H.1

  hott def intro {A : Type u} (H : Structures.hset A)
    (φ : A → A → A) (ι : A → A) (e : A)
    (α : Π a b c, φ (φ a b) c = φ a (φ b c))
    (β₁ : Π a, φ e a = a) (β₂ : Π a, φ a e = a) : Monoid :=
  ⟨Magma.intro H φ, (α, ⟨e, λ a, (β₁ a, β₂ a)⟩)⟩
end Monoid

inductive Term (A : Type u)
| φ : Term A → Term A → Term A
| ι : A → Term A
| e : Term A

hott def Term.toList {A : Type u} : Term A → List A
| Term.φ x y => Term.toList x ++ Term.toList y
| Term.ι x   => [x]
| Term.e     => []

hott def Term.ofList {A : Type u} : List A → Term A
| []      => Term.e
| x :: xs => Term.φ (Term.ι x) (Term.ofList xs)

hott def Term.toMonoid (M : Monoid) : Term M.carrier → M.carrier
| Term.φ x y => M.φ (Term.toMonoid M x) (Term.toMonoid M y)
| Term.ι x   => x
| Term.e     => M.e

hott def Term.ofAppend (M : Monoid) : Π (xs ys : List M.carrier),
    Term.toMonoid M (Term.ofList (xs ++ ys))
  = M.φ (Term.toMonoid M (Term.ofList xs)) (Term.toMonoid M (Term.ofList ys))
| [],      ys => (M.oneMul _)⁻¹
| x :: xs, ys => ap (M.φ x) (Term.ofAppend M xs ys) ⬝ (M.mulAssoc _ _ _)⁻¹

hott def Term.sec (M : Monoid) : Term.toMonoid M ∘ Term.ofList ∘ Term.toList ~ Term.toMonoid M
| Term.e     => Id.refl
| Term.ι x   => M.mulOne x
| Term.φ x y => Term.ofAppend M _ _ ⬝ Equiv.bimap M.φ (Term.sec M x) (Term.sec M y)

hott def Term.solve (M : Monoid) (τ₁ τ₂ : Term M.carrier)
  (ρ : τ₁.toList = τ₂.toList) : τ₁.toMonoid M = τ₂.toMonoid M :=
(Term.sec M τ₁)⁻¹ ⬝ ap (Term.toMonoid M ∘ Term.ofList) ρ ⬝ Term.sec M τ₂

hott def Term.example (M : Monoid) (x y z : M.carrier) :
  M.φ (M.φ (M.φ x (M.φ y M.e)) M.e) (M.φ z M.e) = M.φ x (M.φ y z) :=
Term.solve M (Term.φ (Term.φ (Term.φ (Term.ι x) (Term.φ (Term.ι y) Term.e)) Term.e) (Term.φ (Term.ι z) Term.e))
  (Term.φ (Term.ι x) (Term.φ (Term.ι y) (Term.ι z))) Id.refl

hott def Term.ret {A : Type u} : Term.toList ∘ @Term.ofList A ~ id
| []      => Id.refl
| x :: xs => ap (List.cons x) (Term.ret xs)

end GroundZero.Algebra
