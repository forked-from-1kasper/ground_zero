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

  def le (n m : ℕ) := max n m = m
  infix ` ≤ ` := le

  def ge (n m : ℕ) : Type := m ≤ n
  infix ` ≥ ` := ge

  @[hott] def max.zero_left (n : ℕ) : max 0 n = n :=
  begin induction n; reflexivity end

  @[hott] def max.zero_right (n : ℕ) : max n 0 = n :=
  begin induction n; reflexivity end

  @[hott] def min.zero_left (n : ℕ) : min 0 n = 0 :=
  begin induction n; reflexivity end

  @[hott] def min.zero_right (n : ℕ) : min n 0 = 0 :=
  begin induction n; reflexivity end

  @[hott] def max.ne_zero {n : ℕ} : max (n + 1) 0 = 0 → 𝟎 :=
  begin intro p, apply @ua.succ_neq_zero n, exact p end

  @[hott] def max.zero (n : ℕ) : max n 0 = 0 → n = 0 :=
  begin
    intro p, induction n with n ih, reflexivity,
    apply proto.empty.elim,
    apply @max.ne_zero n, assumption
  end

  @[hott] def le.prop (n m : ℕ) : prop (n ≤ m) :=
  by apply nat_is_set

  @[hott] def max.assoc : Π (n m k : ℕ), max n (max m k) = max (max n m) k
  |    0       0       0    := idp 0
  |    0       0    (k + 1) := idp (k + 1)
  |    0    (m + 1)    0    := idp (m + 1)
  |    0    (m + 1) (k + 1) := max.zero_left (max m k + 1)
  | (n + 1)    0       0    := idp (n + 1)
  | (n + 1)    0    (k + 1) := idp (max n k + 1)
  | (n + 1) (m + 1)    0    := idp (max n m + 1)
  | (n + 1) (m + 1) (k + 1) := (+ 1) # (max.assoc n m k)

  @[hott] def min.assoc : Π (n m k : ℕ), min n (min m k) = min (min n m) k
  |    0       0       0    := idp 0
  |    0       0    (k + 1) := idp 0
  |    0    (m + 1)    0    := idp 0
  |    0    (m + 1) (k + 1) := min.zero_left (min m k + 1)
  | (n + 1)    0       0    := idp 0
  | (n + 1)    0    (k + 1) := idp 0
  | (n + 1) (m + 1)    0    := idp 0
  | (n + 1) (m + 1) (k + 1) := (+ 1) # (min.assoc n m k)

  @[hott, trans] def le.trans (n m k : ℕ) : le n m → le m k → le n k :=
  begin
    intros p q, change _ = _, transitivity,
    apply Id.map, exact q⁻¹, transitivity, apply max.assoc,
    transitivity, apply Id.map (λ p, max p k), exact p, exact q
  end

  @[hott] def le.inj (n m : ℕ) : le (n + 1) (m + 1) → le n m :=
  λ p, nat.pred # p

  @[hott] def le.map (n m : ℕ) : le n m → le (n + 1) (m + 1) :=
  λ p, (+ 1) # p

  @[hott] def le.succ (n : ℕ) : le n (n + 1) :=
  begin
    induction n with n ih, change _ = _, reflexivity,
    apply Id.map (+ 1), exact ih
  end

  @[hott] def le.step (n m : ℕ) : le n m → le n (m + 1) :=
  begin
    intro p, induction n with n ih,
    { change _ = _, reflexivity },
    { transitivity, exact p, apply le.succ }
  end

  @[hott] def min_max : Π (m n : ℕ), max m n = n → min m n = m
  |    0       0    := λ p, idp 0
  | (m + 1)    0    := λ p, proto.empty.elim (max.ne_zero p)
  |    0    (n + 1) := λ p, idp 0
  | (m + 1) (n + 1) := λ p, (+ 1) # (min_max m n (nat.pred # p))

  @[hott] def le.max (n m : ℕ) : le n (max n m) :=
  begin
    change _ = _, transitivity, apply max.assoc,
    apply Id.map (λ p, max p m), apply max.refl
  end

  @[hott] def le.max_rev (n m : ℕ) : le n (max m n) :=
  equiv.transport (le n) (max.comm n m) (le.max n m)

  @[hott] def le.min : Π (n m : ℕ), le (min n m) m
  |    0       0    := idp 0
  | (n + 1)    0    := idp 0
  |    0    (m + 1) := idp (m + 1)
  | (n + 1) (m + 1) := (+ 1) # (le.min n m)

  @[hott] def le.min_rev (n m : ℕ) : le (min m n) m :=
  @equiv.transport ℕ (λ n, le n m) (min n m) (min m n) (min.comm n m) (le.min n m)

  @[hott] def le.asymm {n m : ℕ} : le n m → le m n → n = m :=
  begin intros p q, transitivity, exact q⁻¹, transitivity, apply max.comm, exact p end

  @[hott] def le.dec : Π (m n : ℕ), le m n + le (n + 1) m
  |    0       0    := sum.inl (idp 0)
  | (m + 1)    0    := sum.inr (nat.succ # (max.zero_left m))
  |    0    (n + 1) := sum.inl (idp (n + 1))
  | (m + 1) (n + 1) := coproduct.elim (sum.inl ∘ Id.map nat.succ)
                                      (sum.inr ∘ Id.map nat.succ)
                                      (le.dec m n)

  @[hott] def le.ne_succ (n : ℕ) : le (n + 1) n → 𝟎 :=
  begin intro p, induction n with n ih, apply max.ne_zero p, apply ih, exact le.inj _ _ p end

  @[hott] def le.empty (m n : ℕ) : le m n → le (n + 1) m → 𝟎 :=
  begin intros p q, apply le.ne_succ n, transitivity, exact q, exact p end

  @[hott] def le.neq_succ {n m : ℕ} : neq n (m + 1) → le n (m + 1) → le n m :=
  begin
    intros p q, cases le.dec n m with r₁ r₂, assumption,
    apply proto.empty.elim, apply p, apply le.asymm; assumption
  end

  @[hott] def le.n_le_succ_n (n : ℕ) : le n (n + 1) :=
  begin induction n with n ih, change _ = _, reflexivity, apply Id.map nat.succ, exact ih end

  @[hott] def le.elim (ρ : ℕ → ℕ → Type u)
    (τ : Π n m k, ρ n m → ρ m k → ρ n k)
    (reflρ : Π n, ρ n n) (succρ : Π n, ρ n (n + 1))
    {n m : ℕ} : le n m → ρ n m :=
  begin
    intro p, induction m with m ih,
    { apply equiv.transport (λ n, ρ n 0), symmetry,
      apply max.zero, exact p, apply reflρ },
    { cases nat_dec_eq n (m + 1) with q₁ q₂,
      { apply equiv.transport (ρ n), exact q₁, apply reflρ },
      { apply τ n m, apply ih, apply le.neq_succ, exact q₂,
        exact p, apply succρ } }
  end

  def dist : ℕ → ℕ → ℕ
  |    0       0    := 0
  | (n + 1)    0    := n + 1
  |    0    (m + 1) := m + 1
  | (n + 1) (m + 1) := dist n m

  @[hott] def dist.refl (n : ℕ) : dist n n = 0 :=
  begin induction n with n ih, reflexivity, exact ih end

  @[hott] def dist.identity : Π (n m : ℕ) (p : dist n m = 0), n = m
  |    0       0    p := idp 0
  | (n + 1)    0    p := p
  |    0    (m + 1) p := p⁻¹
  | (n + 1) (m + 1) p := nat.succ # (dist.identity n m p)

  @[hott] def dist.symm : Π (n m : ℕ), dist n m = dist m n
  |    0       0    := idp 0
  | (n + 1)    0    := idp (n + 1)
  |    0    (m + 1) := idp (m + 1)
  | (n + 1) (m + 1) := dist.symm n m

  @[hott] def dist.zero_left (n : ℕ) : dist n 0 = n :=
  begin induction n; reflexivity end

  @[hott] def dist.zero_right (n : ℕ) : dist 0 n = n :=
  begin induction n; reflexivity end

  @[hott] def dist.succ_left : Π (n m : ℕ), le (dist (n + 1) m) (dist n m + 1)
  |    0       0    := idp 1
  | (n + 1)    0    := max.refl (n + 2)
  |    0    (m + 1) := @equiv.transport ℕ (λ k, le k (m + 2)) m (dist 0 m)
    (Id.symm (dist.zero_right m)) (le.trans m (m + 1) (m + 2) (le.n_le_succ_n m) (le.n_le_succ_n (m + 1)))
  | (n + 1) (m + 1) := dist.succ_left n m

  @[hott] def max.le_add : Π (n m : ℕ), le (max n m) (n + m)
  |    0       0    := idp 0
  | (n + 1)    0    := max.refl (n + 1)
  |    0    (m + 1) := @equiv.transport ℕ (le (m + 1)) (m + 1) (0 + (m + 1))
    (Id.symm (zero_plus_i (m + 1))) (max.refl (m + 1))
  | (n + 1) (m + 1) := le.trans (max n m + 1) ((n + m) + 1) ((n + 1) + (m + 1))
    (le.map (max n m) (n + m) (max.le_add n m)) (begin
      apply equiv.transport (le (n + m + 1)), symmetry,
      transitivity, apply nat.assoc, transitivity, transitivity, apply Id.map,
      symmetry, apply nat.assoc, symmetry, apply nat.assoc,
      apply Id.map (λ k, n + k + 1), apply nat.comm, apply le.n_le_succ_n
    end)

  -- ℕ-specific property
  @[hott] def dist.max : Π (n m : ℕ), le (dist n m) (max n m)
  |    0       0    := idp 0
  | (n + 1)    0    := max.refl (n + 1)
  |    0    (m + 1) := max.refl (m + 1)
  | (n + 1) (m + 1) := le.trans (dist n m) (max n m) (max n m + 1) (dist.max n m) (le.n_le_succ_n (max n m))

  @[hott] def dist.le (n m : ℕ) : le (dist n m) (n + m) :=
  le.trans (dist n m) (max n m) (n + m) (dist.max n m) (max.le_add n m)
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