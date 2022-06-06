import GroundZero.HITs.Suspension
open GroundZero.Types.Equiv (pathoverOfEq)
open GroundZero.Types

/-
  Join.
  * HoTT 6.8
-/

namespace GroundZero.HITs

universe u v w
def Join (α : Type u) (β : Type v) :=
@Pushout α β (α × β) Prod.pr₁ Prod.pr₂

namespace Join
  variable {α : Type u} {β : Type v}

  def inl : α → Join α β := Pushout.inl
  def inr : β → Join α β := Pushout.inr

  hott def push (a : α) (b : β) : inl a = inr b :=
  Pushout.glue (a, b)

  hott def ind {π : Join α β → Type w}
    (inlπ : Π (x : α), π (inl x)) (inrπ : Π (x : β), π (inr x))
    (pushπ : Π (a : α) (b : β), inlπ a =[push a b] inrπ b) : Π x, π x :=
  Pushout.ind inlπ inrπ (λ w, pushπ w.1 w.2)

  attribute [eliminator] ind

  hott def rec {π : Type w} (inlπ : α → π) (inrπ : β → π)
    (pushπ : Π a b, inlπ a = inrπ b) : Join α β → π :=
  Pushout.rec inlπ inrπ (λ w, pushπ w.1 w.2)

  hott def fromSusp : ∑ α → Join 𝟐 α :=
  Suspension.rec (inl false) (inl true) (λ x, push false x ⬝ (push true x)⁻¹)

  hott def toSusp : Join 𝟐 α → ∑ α :=
  rec (λ | false => Suspension.north
         | true  => Suspension.south)
      (λ _, Suspension.south)
      (λ | false => Suspension.merid
         | true  => λ _, idp _)
end Join

end GroundZero.HITs