import GroundZero.HITs.Pushout
import GroundZero.Types.Unit

open GroundZero.Types.Equiv
open GroundZero.Types

/-
  Suspension.
  * HoTT 6.5
-/

namespace GroundZero
namespace HITs

def Suspension.{u} (α : Type u) :=
@Pushout.{0, 0, u} 𝟏 𝟏 α (λ _, ★) (λ _, ★)

notation "∑ " => Suspension

namespace Suspension
  -- https://github.com/leanprover/lean2/blob/master/hott/homotopy/susp.hlean
  universe u v

  hott def north {α : Type u} : ∑ α := Pushout.inl ★
  hott def south {α : Type u} : ∑ α := Pushout.inr ★

  hott def merid {α : Type u} (x : α) : @Id (∑ α) north south :=
  Pushout.glue x

  hott def ind {α : Type u} {β : ∑ α → Type v} (n : β north) (s : β south)
    (m : Π x, n =[merid x] s) : Π x, β x :=
  Pushout.ind (λ ★, n) (λ ★, s) m

  attribute [eliminator] ind

  hott def rec {α : Type u} {β : Type v} (n s : β) (m : α → n = s) : ∑ α → β :=
  Pushout.rec (λ _, n) (λ _, s) m

  noncomputable hott def indβrule {α : Type u} {β : ∑ α → Type v}
    (n : β north) (s : β south) (m : Π x, n =[merid x] s) (x : α) :
    apd (ind n s m) (merid x) = m x :=
  by apply Pushout.indβrule

  noncomputable hott def recβrule {α : Type u} {β : Type v} (n s : β)
    (m : α → n = s) (x : α) : Id.map (rec n s m) (merid x) = m x :=
  by apply Pushout.recβrule
end Suspension

end HITs
end GroundZero