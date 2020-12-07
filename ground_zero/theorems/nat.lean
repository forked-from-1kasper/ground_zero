import ground_zero.theorems.ua ground_zero.types.nat
open ground_zero.structures (prop contr)
open ground_zero.types

namespace ground_zero
namespace theorems

hott theory

namespace nat
  universe u

  @[hott] noncomputable def nat_is_set' : structures.hset ℕ
  |    0       0    p q :=
    types.equiv.transport
      structures.prop (ua $ types.nat.recognize 0 0)⁻¹
      structures.unit_is_prop p q
  | (m + 1)    0    p q := by cases ua.succ_neq_zero p
  |    0    (n + 1) p q := by cases ua.succ_neq_zero p⁻¹
  | (m + 1) (n + 1) p q := begin
    refine types.equiv.transport structures.prop
           (ua $ types.nat.recognize (m + 1) (n + 1))⁻¹ _ p q,
    apply types.equiv.transport structures.prop (ua $ types.nat.recognize m n),
    apply nat_is_set'
  end

  def succ_inj {n m : ℕ} : nat.succ n = nat.succ m → n = m :=
  nat.decode ∘ nat.encode

  @[hott] def nat_dec_eq : Π (n m : ℕ), structures.dec (n = m)
  |    0       0    := sum.inl (idp 0)
  |    0    (m + 1) := sum.inr (λ p, ua.succ_neq_zero p⁻¹)
  | (n + 1)    0    := sum.inr ua.succ_neq_zero
  | (n + 1) (m + 1) :=
    match nat_dec_eq n m with
    | sum.inl p := sum.inl (nat.succ # p)
    | sum.inr f := sum.inr (λ p, f (succ_inj p))
    end
  
  @[hott] def nat_is_set : structures.hset ℕ :=
  λ n m, structures.Hedberg nat_dec_eq

  @[hott] def zero_plus_i (i : ℕ) : 0 + i = i :=
  begin
    induction i with i ih,
    { trivial },
    { apply Id.map nat.succ, assumption }
  end

  @[hott] def succ_i_plus_j (i j : ℕ) : nat.succ i + j = nat.succ (i + j) :=
  begin
    induction j with j ih,
    { trivial },
    { apply Id.map nat.succ, assumption }
  end

  @[hott] def comm (i j : ℕ) : i + j = j + i :=
  begin
    induction i with i ih,
    { apply zero_plus_i },
    { transitivity, apply succ_i_plus_j,
      apply Id.map, assumption }
  end

  @[hott] def assoc (i j k : ℕ) : (i + j) + k = i + (j + k) :=
  begin
    induction k with k ih,
    { trivial }, { apply Id.map nat.succ, exact ih }
  end

  @[hott] def zero_mul_n (i : ℕ) : 0 * i = 0 :=
  begin
    induction i with i ih,
    trivial, exact ih
  end

  @[hott] def one_mul (i : ℕ) : 1 * i = i :=
  begin
    induction i with i ih, { reflexivity },
    { apply Id.map nat.succ, assumption }
  end

  @[hott] def distrib_left (i j n : ℕ) : n * (i + j) = n * i + n * j :=
  begin
    induction j with j ih,
    { trivial },
    { transitivity, apply Id.map (+ n), exact ih,
      transitivity, apply assoc, trivial }
  end

  @[hott] def mul_succ_i_j (i j : ℕ) : nat.succ i * j = i * j + j :=
  begin
    induction j with j ih,
    { trivial },
    { apply Id.map nat.succ,
      transitivity, apply Id.map (+ i), exact ih,
      transitivity, apply assoc,
      symmetry, transitivity, apply assoc,
      apply Id.map, apply comm }
  end

  @[hott] def mul_comm (i j : ℕ) : i * j = j * i :=
  begin
    induction j with j ih,
    { symmetry, apply zero_mul_n },
    { transitivity, apply distrib_left j 1,
      symmetry, transitivity, apply mul_succ_i_j j i,
      transitivity, apply Id.map (+ i), exact ih⁻¹,
      apply Id.map (λ x, (i * j) + x),
      symmetry, apply zero_plus_i }
  end

  @[hott] def mul_one (i : ℕ) : i * 1 = i :=
  mul_comm i 1 ⬝ one_mul i

  @[hott] def distrib_right (i j n : ℕ) : (i + j) * n = i * n + j * n :=
  begin
    transitivity, apply mul_comm,
    symmetry, transitivity, apply Id.map, apply mul_comm,
    transitivity, apply Id.map (+ n * j), apply mul_comm,
    symmetry, apply distrib_left
  end

  @[hott] def one_neq_n_plus_two (n : ℕ) : ¬(1 = n + 2) :=
  λ h, ua.succ_neq_zero (nat.pred # h)⁻¹

  def is_even (n : ℕ) := Σ m, n = m * 2
  def is_odd (n : ℕ) := Σ m, n = m * 2 + 1

  @[hott] def i_plus_one_plus_j {i j : ℕ} : i + 1 + j = (i + j) + 1 := calc
    i + 1 + j = i + (1 + j) : by apply assoc
          ... = i + (j + 1) : nat.add i # (comm 1 j)
          ... = (i + j) + 1 : by trivial

  @[hott] def assoc_tetra {i j k l : ℕ} : i + (j + k) + l = (i + j) + (k + l) := calc
    (i + (j + k)) + l = i + ((j + k) + l) : by apply assoc
                  ... = i + (j + (k + l)) : begin apply Id.map, apply assoc end
                  ... = (i + j) + (k + l) : begin symmetry, apply assoc end

  @[hott] def n_plus_n (n : ℕ) : n * 2 = n + n :=
  begin apply Id.map (+ n), apply zero_plus_i end

  @[hott] def apart : ℕ → ℕ → Type
  |    0       0    := 𝟎
  | (m + 1)    0    := 𝟏
  |    0    (n + 1) := 𝟏
  | (m + 1) (n + 1) := apart m n

  @[hott] def max : ℕ → ℕ → ℕ
  |    0       0    := 0
  | (m + 1)    0    := m + 1
  |    0    (n + 1) := n + 1
  | (m + 1) (n + 1) := max m n + 1

  @[hott] def max.comm : Π (m n : ℕ), max m n = max n m
  |    0       0    := idp 0
  | (m + 1)    0    := idp (m + 1)
  |    0    (n + 1) := idp (n + 1)
  | (m + 1) (n + 1) := (+ 1) # (max.comm m n)

  @[hott] def min : ℕ → ℕ → ℕ
  |    0       0    := 0
  | (m + 1)    0    := 0
  |    0    (n + 1) := 0
  | (m + 1) (n + 1) := min m n + 1

  @[hott] def min.comm : Π (m n : ℕ), min m n = min n m
  |    0       0    := idp 0
  | (m + 1)    0    := idp 0
  |    0    (n + 1) := idp 0
  | (m + 1) (n + 1) := (+ 1) # (min.comm m n)

  @[hott] def max.refl (n : ℕ) : max n n = n :=
  begin
    induction n with n ih,
    { reflexivity },
    { apply Id.map (+ 1), assumption }
  end

  @[hott] def min.refl (n : ℕ) : min n n = n :=
  begin
    induction n with n ih,
    { reflexivity },
    { apply Id.map (+ 1), assumption }
  end

  inductive lt (n : ℕ) : ℕ → Type
  | refl : lt n
  | step : Π {m}, lt m → lt (m + 1)
  infix ≤ := lt

  @[hott] def gt (n m : ℕ) : Type := m ≤ n
  infix ≥ := gt
end nat

namespace unit_list
  universe u

  def zero' : list 𝟏 := []
  def succ' : list 𝟏 → list 𝟏 :=
  list.cons ★

  def ind' {E : list 𝟏 → Type u}
    (e₀ : E zero') (eₛ : Π (n : list 𝟏), E n → E (succ' n)) :
    Π (n : list 𝟏), E n
  | [] := e₀
  | (★ :: tail) := eₛ tail (ind' tail)

  def encode : ℕ → list 𝟏
  | 0 := zero'
  | (n + 1) := succ' (encode n)

  def decode : list 𝟏 → ℕ
  | [] := nat.zero
  | (_ :: tail) := nat.succ (decode tail)

  @[hott] theorem nat_isomorphic : ℕ ≃ list 𝟏 :=
  begin
    existsi encode, split; existsi decode,
    { intro n, induction n with n ih,
      { trivial },
      { apply Id.map nat.succ, exact ih } },
    { intro l, induction l with head tail ih,
      { trivial },
      { induction head, apply Id.map succ', exact ih } }
  end

  @[hott] noncomputable def nat_equality : ℕ = list 𝟏 :=
  ua nat_isomorphic
end unit_list

end theorems
end ground_zero