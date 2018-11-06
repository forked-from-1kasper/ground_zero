import ground_zero.eq

namespace ground_zero.support
  universe u

  def inclusion {α : Sort u} {a b : α} (p : eq a b) : a = b :> α :=
  begin induction p, reflexivity end

  def truncation {α : Sort u} {a b : α} (p : a = b :> α) : eq a b :=
  begin induction p, reflexivity end

  instance inclusion_coe {α : Sort u} {a b : α} : has_coe (eq a b) (a = b :> α) :=
  ⟨inclusion⟩

  instance truncation_coe {α : Sort u} {a b : α} : has_coe (a = b :> α) (eq a b) :=
  ⟨truncation⟩
end ground_zero.support