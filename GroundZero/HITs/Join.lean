import GroundZero.HITs.Suspension

open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Types
open GroundZero.Proto
open Prod (pr₁ pr₂)

/-
  Join.
  * HoTT 6.8
-/

namespace GroundZero.HITs

universe u v w u' v' w'

hott definition Join (A : Type u) (B : Type v) :=
@Pushout A B (A × B) pr₁ pr₂

infixl:70 " ∗ " => Join

namespace Join
  variable {A : Type u} {B : Type v}

  hott definition inl : A → A ∗ B := Pushout.inl
  hott definition inr : B → A ∗ B := Pushout.inr

  hott definition glue (a : A) (b : B) : inl a = inr b :=
  Pushout.glue (a, b)

  hott definition ind {C : A ∗ B → Type w}
    (inlπ : Π (x : A), C (inl x)) (inrπ : Π (x : B), C (inr x))
    (pushπ : Π (a : A) (b : B), inlπ a =[glue a b] inrπ b) : Π x, C x :=
  Pushout.ind inlπ inrπ (λ w, pushπ w.1 w.2)

  attribute [induction_eliminator] ind

  hott definition rec {C : Type w} (f : A → C) (g : B → C) (H : Π a b, f a = g b) : A ∗ B → C :=
  Pushout.rec f g (λ w, H w.1 w.2)

  hott definition recβrule {C : Type w} (f : A → C) (g : B → C) (H : Π a b, f a = g b) (a : A) (b : B) :
    ap (rec f g H) (glue a b) = H a b :=
  by apply Pushout.recβrule

  hott definition fromSusp : ∑ A → 𝟐 ∗ A :=
  Suspension.rec (inl false) (inl true) (λ x, glue false x ⬝ (glue true x)⁻¹)

  hott definition toSusp : 𝟐 ∗ A → ∑ A :=
  rec (λ | false => Suspension.north
         | true  => Suspension.south)
      (λ _, Suspension.south)
      (λ | false => Suspension.merid
         | true  => λ _, idp _)
end Join

end GroundZero.HITs
