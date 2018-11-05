import ground_zero.eq

namespace ground_zero.support
  universe u

  def of_builtin {α : Sort u} {a b : α} (p : eq a b) : a = b :> α :=
  begin induction p, reflexivity end

  def to_builtin {α : Sort u} {a b : α} (p : a = b :> α) : eq a b :=
  begin induction p, reflexivity end

  instance of_builtin_coe {α : Sort u} {a b : α} : has_coe (eq a b) (a = b :> α) :=
  ⟨of_builtin⟩

  instance to_builtin_coe {α : Sort u} {a b : α} : has_coe (a = b :> α) (eq a b) :=
  ⟨to_builtin⟩
end ground_zero.support