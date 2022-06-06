import GroundZero.Types.Id

namespace GroundZero.Support
  universe u

  -- this is unsafe
  def inclusion {A : Type u} {a b : A} (p : Eq a b) : a = b :=
  begin induction p; reflexivity end

  hott def truncation {A : Type u} {a b : A} (p : a = b) : Eq a b :=
  begin induction p; reflexivity end
end GroundZero.Support