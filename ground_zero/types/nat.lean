import ground_zero.structures ground_zero.HITs.colimit
open ground_zero.types

namespace ground_zero.types.nat

universes u v w

def glue : ℕ → ℕ + 𝟏
| nat.zero := coproduct.inr ★
| (nat.succ n) := coproduct.inl n

def peel_off : ℕ + 𝟏 → ℕ
| (coproduct.inr _) := nat.zero
| (coproduct.inl n) := nat.succ n

theorem closed_nat : ℕ ≃ ℕ + 𝟏 := begin
  existsi glue, split; existsi peel_off,
  { intro n, induction n with n ih,
    { simp [peel_off, glue] },
    { simp at ih, simp, simp [glue, peel_off] } },
  { intro n, simp, induction n,
    { simp [peel_off, glue] },
    { induction n, simp [glue, peel_off] } }
end

theorem equiv_addition {α : Sort u} {β : Sort v} (γ : Sort w)
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

example : ℕ ≃ ℕ + 𝟏 + 𝟏 := begin
  transitivity, exact closed_nat,
  apply equiv_addition, exact closed_nat
end

def drop (α : Type) : ℕ → Type
| 0 := α
| (nat.succ n) := coproduct (drop n) (𝟏 : Type)

theorem nat_plus_unit (n : ℕ) : ℕ ≃ drop ℕ n := begin
  induction n with n ih,
  { reflexivity },
  { transitivity,
    exact closed_nat,
    apply equiv_addition 𝟏 ih }
end

abbreviation lift_unit (n : ℕ) : drop 𝟏 n → drop 𝟏 (n + 1) :=
coproduct.inl

def lift_to_top (x : 𝟏) : Π (n : ℕ), drop 𝟏 n
| 0 := x
| (n + 1) := coproduct.inl (lift_to_top n)

def iterated := ground_zero.HITs.colimit (drop 𝟏) lift_unit

def iterated.encode : ℕ → iterated
| 0 := ground_zero.HITs.colimit.inclusion 0 ★
| (n + 1) := ground_zero.HITs.colimit.inclusion (n + 1) (coproduct.inr ★)

def code : ℕ → ℕ → Type
|    0       0    := 𝟏
| (m + 1)    0    := 𝟎
|    0    (n + 1) := 𝟎
| (m + 1) (n + 1) := code m n

def r : Π n, code n n
| 0 := ★
| (n + 1) := r n

def encode {m n : ℕ} (p : m = n :> ℕ) : code m n :=
equiv.subst p (r m)

def decode : Π {m n : ℕ}, code m n → (m = n :> ℕ)
|    0       0    p := by reflexivity
| (m + 1)    0    p := by cases p
|    0    (n + 1) p := by cases p
| (m + 1) (n + 1) p := begin
  apply eq.map nat.succ, apply decode, exact p
end

def decode_encode {m n : ℕ} (p : m = n :> ℕ) : decode (encode p) = p :> _ :=
begin
  induction p, induction m with m ih,
  { reflexivity },
  { clear n, unfold encode, unfold decode, unfold r,
    transitivity, apply eq.map, apply ih, reflexivity }
end

def encode_decode : Π {m n : ℕ} (p : code m n), encode (decode p) = p :> _
|    0       0    p := begin cases p, reflexivity end
| (m + 1)    0    p := by cases p
|    0    (n + 1) p := by cases p
| (m + 1) (n + 1) p := begin
  transitivity, symmetry,
  apply @equiv.transport_comp ℕ ℕ (code (m + 1)) m n
        nat.succ (decode p) (r (m + 1)),
  apply encode_decode
end

def recognize (m n : ℕ) : (m = n :> ℕ) ≃ code m n := begin
  existsi encode, split; existsi decode,
  apply decode_encode, apply encode_decode
end

end ground_zero.types.nat