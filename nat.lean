import ground_zero.equiv ground_zero.coproduct
import ground_zero.support
open ground_zero

namespace ground_zero.nat

universes u v w

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

theorem equiv_addition (α : Type u) (β : Type v) (γ : Type w)
  (e : α ≃ β) : α + γ ≃ β + γ := begin
  induction e with f H,
  have q := qinv.b2q f H,
  cases q with g inv, cases inv with α' β',

  simp [equiv.homotopy, function.comp] at α',
  simp [equiv.homotopy, function.comp] at β',

  let f : α + γ → β + γ := λ x, match x with
  | coproduct.inl a := coproduct.inl (f a)
  | coproduct.inr c := coproduct.inr c
  end,
  let g : β + γ → α + γ := λ x, match x with
  | coproduct.inl b := coproduct.inl (g b)
  | coproduct.inr c := coproduct.inr c
  end,

  existsi f, split; existsi g,
  { intro x, induction x,
    { simp [g, f],
      rw [support.to_builtin (β' x)],
      simp },
    { trivial } },
  { intro x, induction x,
    { simp [f, g],
      rw [support.to_builtin (α' x)],
      simp },
    { trivial } }
end

end ground_zero.nat