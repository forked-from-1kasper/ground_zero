import ground_zero.eq

namespace ground_zero.support
  universe u

  def of_builtin {α : Sort u} {a b : α} (p : eq a b) : a = b :> α :=
  begin induction p, reflexivity end

  def to_builtin {α : Sort u} {a b : α} (p : a = b :> α) : eq a b :=
  begin induction p, reflexivity end
end ground_zero.support