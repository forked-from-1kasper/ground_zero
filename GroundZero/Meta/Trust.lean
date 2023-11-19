import GroundZero.Types.Id
open GroundZero.Types

universe u

namespace GroundZero
  /--
    Used to postulate propositional computation rules for higher constructors.

    Shouldn’t be used directly (hence marked as `nothott`).
  -/
  opaque trustCoherence {A : Type u} {a b : A} {p q : a = b} : p = q :=
  match p, q with | idp _, idp _ => idp _

  /--
    Used to generate 1-path constructors out of `Quot.sound`.

    Should be used only within of `opaque` (hence marked as `nothott`).
  -/
  def trustHigherCtor {A : Type u} {a b : A} (p : Eq a b) : a = b :=
  begin induction p; reflexivity end

  attribute [nothott] trustCoherence trustHigherCtor

  hott def elimEq {A : Type u} {a b : A} (p : a = b) : Eq a b :=
  begin induction p; reflexivity end
end GroundZero
