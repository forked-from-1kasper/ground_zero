import ground_zero.types.eq

attribute [nothott] quot.lift quot.ind quot.rec classical.choice

namespace ground_zero.support
  universe u

  -- this is unsafe
  def inclusion {α : Type u} {a b : α} (p : eq a b) : a = b :> α :=
  begin induction p, reflexivity end

  @[hott] def truncation {α : Type u} {a b : α} (p : a = b :> α) : eq a b :=
  begin induction p, reflexivity end
end ground_zero.support