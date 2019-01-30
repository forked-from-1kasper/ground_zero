import ground_zero.types.coproduct ground_zero.HITs.colimit
open ground_zero.types

namespace ground_zero.types.nat

universes u v w

def encode : ℕ → ℕ + unit
| nat.zero := coproduct.inr unit.star
| (nat.succ n) := coproduct.inl n

def decode : ℕ + unit → ℕ
| (coproduct.inr _) := nat.zero
| (coproduct.inl n) := nat.succ n

theorem closed_nat : ℕ ≃ ℕ + unit := begin
  existsi encode, split; existsi decode,
  { intro n, induction n with n ih,
    { simp [decode, encode] },
    { simp at ih, simp, simp [encode, decode] } },
  { intro n, simp, induction n,
    { simp [decode, encode] },
    { induction n, simp [encode, decode] } }
end

theorem equiv_addition {α : Type u} {β : Type v} (γ : Type w)
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
      rw [ground_zero.support.truncation (β' x)],
      simp },
    { trivial } },
  { intro x, induction x,
    { simp [f, g],
      rw [ground_zero.support.truncation (α' x)],
      simp },
    { trivial } }
end

example : ℕ ≃ ℕ + unit + unit := begin
  transitivity, exact closed_nat,
  apply equiv_addition, exact closed_nat
end

def drop (α : Type) : ℕ → Type
| 0 := α
| (nat.succ n) := coproduct (drop n) unit

theorem nat_plus_unit (n : ℕ) : ℕ ≃ drop ℕ n := begin
  induction n with n ih,
  { reflexivity },
  { transitivity,
    exact closed_nat,
    apply equiv_addition unit ih }
end

abbreviation lift_unit (n : ℕ) : drop unit n → drop unit (n + 1) :=
coproduct.inl

def lift_to_top (x : unit) : Π (n : ℕ), drop unit n
| 0 := x
| (n + 1) := coproduct.inl (lift_to_top n)

def iterated := ground_zero.HITs.colimit (drop unit) lift_unit

def iterated.encode : ℕ → iterated
| 0 := ground_zero.HITs.colimit.inclusion 0 unit.star
| (n + 1) := ground_zero.HITs.colimit.inclusion (n + 1) (coproduct.inr unit.star)

end ground_zero.types.nat