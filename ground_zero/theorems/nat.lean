import ground_zero.theorems.ua ground_zero.types.nat

namespace ground_zero
namespace theorems

hott theory

namespace nat
  noncomputable def nat_is_set : ground_zero.structures.hset ℕ
  |    0       0    p q :=
    types.equiv.transport
      structures.prop (ua $ types.nat.recognize 0 0)⁻¹
      structures.unit_is_prop p q
  | (m + 1)    0    p q := by cases p
  |    0    (n + 1) p q := by cases p
  | (m + 1) (n + 1) p q := begin
    refine types.equiv.transport structures.prop
           (ua $ types.nat.recognize (m + 1) (n + 1))⁻¹ _ p q,
    apply types.equiv.transport structures.prop (ua $ types.nat.recognize m n),
    apply nat_is_set
  end

  def zero_plus_i (i : ℕ) : 0 + i = i := begin
    induction i with i ih,
    { trivial },
    { apply types.eq.map nat.succ, assumption }
  end

  def succ_i_plus_j (i j : ℕ) : nat.succ i + j = nat.succ (i + j) := begin
    induction j with j ih,
    { trivial },
    { apply types.eq.map nat.succ, assumption }
  end

  def comm (i j : ℕ) : i + j = j + i := begin
    induction i with i ih,
    { apply zero_plus_i },
    { transitivity, apply succ_i_plus_j,
      apply types.eq.map, assumption }
  end
end nat

end theorems
end ground_zero