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

def Suspension.{u} (A : Type u) :=
@Pushout.{0, 0, u} 𝟏 𝟏 A (λ _, ★) (λ _, ★)

notation "∑ " => Suspension

namespace Suspension
  -- https://github.com/leanprover/lean2/blob/master/hott/homotopy/susp.hlean
  universe u v

  hott def north {A : Type u} : ∑ A := Pushout.inl ★
  hott def south {A : Type u} : ∑ A := Pushout.inr ★

  hott def merid {A : Type u} (x : A) : @Id (∑ A) north south :=
  Pushout.glue x

  hott def ind {A : Type u} {B : ∑ A → Type v} (n : B north) (s : B south)
    (m : Π x, n =[merid x] s) : Π x, B x :=
  Pushout.ind (λ ★, n) (λ ★, s) m

  attribute [eliminator] ind

  hott def rec {A : Type u} {B : Type v} (n s : B) (m : A → n = s) : ∑ A → B :=
  Pushout.rec (λ _, n) (λ _, s) m

  noncomputable hott def indβrule {A : Type u} {B : ∑ A → Type v}
    (n : B north) (s : B south) (m : Π x, n =[merid x] s) (x : A) :
    apd (ind n s m) (merid x) = m x :=
  by apply Pushout.indβrule

  noncomputable hott def recβrule {A : Type u} {B : Type v} (n s : B)
    (m : A → n = s) (x : A) : Id.map (rec n s m) (merid x) = m x :=
  by apply Pushout.recβrule
end Suspension

end HITs
end GroundZero