import ground_zero.theorems.ua ground_zero.types.nat
open ground_zero.types

namespace ground_zero
namespace theorems

hott theory

namespace nat
  universe u

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

  def assoc (i j k : ℕ) : (i + j) + k = i + (j + k) := begin
    induction k with k ih,
    { trivial }, { apply eq.map nat.succ, exact ih }
  end

  def zero_mul_n (i : ℕ) : 0 * i = 0 := begin
    induction i with i ih,
    trivial, exact ih
  end

  def distrib_left (i j n : ℕ) : n * (i + j) = n * i + n * j := begin
    induction j with j ih,
    { trivial },
    { transitivity, apply eq.map (+ n), exact ih,
      transitivity, apply assoc, trivial }
  end

  def mul_succ_i_j (i j : ℕ) : nat.succ i * j = i * j + j := begin
    induction j with j ih,
    { trivial },
    { apply eq.map nat.succ,
      transitivity, apply eq.map (+ i), exact ih,
      transitivity, apply assoc,
      symmetry, transitivity, apply assoc,
      apply eq.map, apply comm }
  end

  def mul_comm (i j : ℕ) : i * j = j * i := begin
    induction j with j ih,
    { symmetry, apply zero_mul_n },
    { transitivity, apply distrib_left j 1,
      symmetry, transitivity, apply mul_succ_i_j j i,
      transitivity, apply eq.map (+ i), exact ih⁻¹,
      apply eq.map (λ x, (i * j) + x),
      symmetry, apply zero_plus_i }
  end

  def distrib_right (i j n : ℕ) : (i + j) * n = i * n + j * n := begin
    transitivity, apply mul_comm,
    symmetry, transitivity, apply eq.map, apply mul_comm,
    transitivity, apply eq.map (+ n * j), apply mul_comm,
    symmetry, apply distrib_left
  end

  def dec : ℕ → ℕ
  | 0 := 0
  | 1 := 0
  | (n + 1) := n

  def one_neq_n_plus_two (n : ℕ) : ¬(1 = n + 2) :=
  λ h, ua.succ_neq_zero (dec # h)⁻¹

  mutual inductive even, odd
  with even : ℕ → Type
  | zero : even 0
  | succ {n : ℕ} : odd n → even (nat.succ n)
  with odd : ℕ → Type
  | succ {n : ℕ} : even n → odd (nat.succ n)

  def even_to_odd {n : ℕ} : even (n + 1) → odd n
  | (even.succ h) := h

  def odd_to_even {n : ℕ} : odd (n + 1) → even n
  | (odd.succ h) := h

  mutual def even_dec, odd_dec
  with even_dec : Π n, structures.dec (even n)
  | 0 := coproduct.inl even.zero
  | (n + 1) := match odd_dec n with
    | coproduct.inl h := coproduct.inl (even.succ h)
    | coproduct.inr h := coproduct.inr (h ∘ even_to_odd)
  end
  with odd_dec : Π n, structures.dec (odd n)
  | 0 := begin apply coproduct.inr, intro x, cases x end
  | (n + 1) := match even_dec n with
    | coproduct.inl h := coproduct.inl (odd.succ h)
    | coproduct.inr h := coproduct.inr (h ∘ odd_to_even)
  end

  def parity : Π n, even n + odd n
  | 0 := coproduct.inl even.zero
  | (n + 1) := match parity n with
    | coproduct.inl h := coproduct.inr (odd.succ h)
    | coproduct.inr h := coproduct.inl (even.succ h)
  end

  def is_even (n : ℕ) := Σ m, n = m * 2
  def is_odd (n : ℕ) := Σ m, n = m * 2 + 1

  mutual def even_to_sigma, odd_to_sigma
  with even_to_sigma : Π {n : ℕ}, even n → is_even n
  | 0 even.zero := ⟨0, eq.rfl⟩
  | (nat.succ n) (even.succ h) := match odd_to_sigma h with
    | ⟨m, h⟩ := ⟨m + 1, begin
      transitivity, exact nat.succ # h,
      transitivity, apply assoc (m * 2) 1 1,
      symmetry, apply distrib_right
    end⟩
  end
  with odd_to_sigma : Π {n : ℕ}, odd n → is_odd n
  | (nat.succ n) (odd.succ h) := match even_to_sigma h with
    | ⟨m, h⟩ := ⟨m, nat.succ # h⟩
  end

  def odd_even {σ : ℕ → Sort u}
    (h : Π n, σ (n * 2)) (g : Π n, σ (n * 2 + 1)) (n : ℕ) : σ n :=
  match parity n with
  | coproduct.inl x :=
    match even_to_sigma x with
    | ⟨m, p⟩ := equiv.subst p⁻¹ (h m)
    end
  | coproduct.inr y :=
    match odd_to_sigma y with
    | ⟨m, p⟩ := equiv.subst p⁻¹ (g m)
    end
  end
end nat

end theorems
end ground_zero