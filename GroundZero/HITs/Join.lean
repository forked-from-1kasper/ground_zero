import GroundZero.HITs.Suspension
open GroundZero.Types.Equiv (pathoverOfEq)
open GroundZero.Types

/-
  Join.
  * HoTT 6.8
-/

namespace GroundZero.HITs

universe u v w
def Join (A : Type u) (B : Type v) :=
@Pushout A B (A × B) Prod.pr₁ Prod.pr₂

namespace Join
  variable {A : Type u} {B : Type v}

  def inl : A → Join A B := Pushout.inl
  def inr : B → Join A B := Pushout.inr

  hott def push (a : A) (b : B) : inl a = inr b :=
  Pushout.glue (a, b)

  hott def ind {C : Join A B → Type w}
    (inlπ : Π (x : A), C (inl x)) (inrπ : Π (x : B), C (inr x))
    (pushπ : Π (a : A) (b : B), inlπ a =[push a b] inrπ b) : Π x, C x :=
  Pushout.ind inlπ inrπ (λ w, pushπ w.1 w.2)

  attribute [eliminator] ind

  hott def rec {C : Type w} (inlπ : A → C) (inrπ : B → C)
    (pushπ : Π a b, inlπ a = inrπ b) : Join A B → C :=
  Pushout.rec inlπ inrπ (λ w, pushπ w.1 w.2)

  hott def fromSusp : ∑ A → Join 𝟐 A :=
  Suspension.rec (inl false) (inl true) (λ x, push false x ⬝ (push true x)⁻¹)

  hott def toSusp : Join 𝟐 A → ∑ A :=
  rec (λ | false => Suspension.north
         | true  => Suspension.south)
      (λ _, Suspension.south)
      (λ | false => Suspension.merid
         | true  => λ _, idp _)
end Join

end GroundZero.HITs