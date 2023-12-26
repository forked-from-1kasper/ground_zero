import GroundZero.HITs.Pushout
import GroundZero.Types.Unit

open GroundZero.Types.Equiv
open GroundZero.Types

/-
  Wedge sum.
  * HoTT 6.8
-/

namespace GroundZero
namespace HITs

universe u

hott definition Wedge (A B : Type⁎) :=
@Pushout.{_, _, 0} A.1 B.1 𝟏 (λ _, A.2) (λ _, B.2)

infix:50 " ∨ " => Wedge

namespace Wedge
  variable {A B : Type⁎}

  hott definition inl : A.1 → A ∨ B := Pushout.inl
  hott definition inr : B.1 → A ∨ B := Pushout.inr

  hott definition glue : inl A.2 = inr B.2 :=
  Pushout.glue ★

  hott definition ind {C : A ∨ B → Type u} (inlπ : Π x, C (inl x)) (inrπ : Π x, C (inr x))
    (glueπ : inlπ A.2 =[glue] inrπ B.2) : Π x, C x :=
  Pushout.ind inlπ inrπ (λ ★, glueπ)

  attribute [eliminator] ind

  hott definition rec {C : Type u} (inlπ : A.1 → C) (inrπ : B.1 → C)
    (glueπ : inlπ A.2 = inrπ B.2) : A ∨ B → C :=
  Pushout.rec inlπ inrπ (λ ★, glueπ)
end Wedge

end HITs
end GroundZero
