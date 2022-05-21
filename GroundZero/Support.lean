import GroundZero.Types.Id

namespace GroundZero.Support
  universe u

  -- this is unsafe
  def inclusion {α : Type u} {a b : α} (p : Eq a b) : a = b :=
  begin induction p; reflexivity end

  hott def truncation {α : Type u} {a b : α} (p : a = b) : Eq a b :=
  begin induction p; apply Eq.refl end
end GroundZero.Support