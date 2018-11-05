import ground_zero.equiv ground_zero.coproduct
open ground_zero

namespace ground_zero.nat

def code : ℕ → ℕ + unit
| nat.zero := coproduct.inr unit.star
| (nat.succ n) := coproduct.inl n

def decode : ℕ + unit → ℕ
| (coproduct.inr _) := nat.zero
| (coproduct.inl n) := nat.succ n

theorem closed_nat : ℕ ≃ ℕ + unit := begin
  existsi code, split; existsi decode,
  { intro n, induction n with n ih,
    { simp [decode, code] },
    { simp at ih, simp, simp [code, decode] } },
  { intro n, simp, induction n,
    { simp [decode, code] },
    { induction n, simp [code, decode] } }
end

end ground_zero.nat