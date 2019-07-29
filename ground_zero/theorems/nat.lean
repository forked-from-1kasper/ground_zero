import ground_zero.theorems.ua ground_zero.types.nat ground_zero.types.sigma
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

  def one_neq_n_plus_two (n : ℕ) : ¬(1 = n + 2) :=
  λ h, ua.succ_neq_zero (nat.pred # h)⁻¹

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

  def not_even_impls_odd {n : ℕ} (h : ¬even n) : odd n :=
  match parity n with
  | coproduct.inl g := not.absurd g h
  | coproduct.inr g := g
  end

  def not_odd_impls_even {n : ℕ} (h : ¬odd n) : even n :=
  match parity n with
  | coproduct.inl g := g
  | coproduct.inr g := not.absurd g h
  end

  def is_even (n : ℕ) := Σ' m, n = m * 2
  def is_odd (n : ℕ) := Σ' m, n = m * 2 + 1

  def succ_inj {n m : ℕ} : nat.succ n = nat.succ m → n = m :=
  nat.decode ∘ nat.encode

  def mul_div_right (n : ℕ) {m : ℕ} (H : m > 0) : m * n / m = n :=
  begin induction n; simp [*] end

  def mul_div_left (m : ℕ) {n : ℕ} (H : n > 0) : m * n / n = m := begin
    transitivity, apply eq.map (/ n), apply mul_comm,
    apply mul_div_right, assumption
  end

  def mul_succ_n_inj {i j n : ℕ} (h : i * (n + 1) = j * (n + 1)) : i = j :=
  let h : i * (n + 1) / (n + 1) = j * (n + 1) / (n + 1) := (/ nat.succ n) # h in
  (mul_div_left i $ nat.zero_lt_succ n)⁻¹ ⬝ h ⬝ mul_div_left j (nat.zero_lt_succ n)

  noncomputable def is_even_is_prop (n : ℕ) : structures.prop (is_even n) := begin
    intros x y, cases x with i h, cases y with j g,
    fapply types.sigma.prod,
    { apply mul_succ_n_inj, exact h⁻¹ ⬝ g },
    { apply nat_is_set }
  end

  noncomputable def is_odd_is_prop (n : ℕ) : structures.prop (is_odd n) := begin
    intros x y, cases x with i h,cases y with j g,
    fapply types.sigma.prod,
    { apply mul_succ_n_inj, apply succ_inj, exact h⁻¹ ⬝ g },
    { apply nat_is_set }
  end

  mutual def even_is_prop, odd_is_prop
  with even_is_prop : Π n, structures.prop (even n)
  | 0 even.zero even.zero := eq.rfl
  | (n + 1) (even.succ h) (even.succ g) := even.succ # (odd_is_prop n h g)
  with odd_is_prop : Π n, structures.prop (odd n)
  | (n + 1) (odd.succ h) (odd.succ g) := odd.succ # (even_is_prop n h g)

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

  mutual def even_plus_even_is_even, odd_plus_odd_is_even
  with even_plus_even_is_even : Π {n m : ℕ}, even n → even m → even (n + m)
  | 0 0 even.zero even.zero := even.zero
  | 0 _ even.zero g := equiv.subst (zero_plus_i _)⁻¹ g
  | _ 0 h even.zero := h
  | (n + 1) (m + 1) (even.succ h) (even.succ g) :=
    even.succ (equiv.subst (succ_i_plus_j n m)⁻¹ $ odd.succ $
                odd_plus_odd_is_even h g)
  with odd_plus_odd_is_even : Π {n m : ℕ}, odd n → odd m → even (n + m)
  | (n + 1) (m + 1) (odd.succ h) (odd.succ g) :=
    even.succ (equiv.subst (succ_i_plus_j n m)⁻¹ $ odd.succ $
                even_plus_even_is_even h g)

  def i_plus_one_plus_j {i j : ℕ} : i + 1 + j = (i + j) + 1 := calc
    i + 1 + j = i + (1 + j) : by apply assoc
          ... = i + (j + 1) : nat.add i # (comm 1 j)
          ... = (i + j) + 1 : by trivial

  mutual def even_plus_two, odd_plus_two
  with even_plus_two : Π {n : ℕ}, even n → even (n + 2)
  | 0 even.zero := even.succ (odd.succ even.zero)
  | (n + 1) (even.succ h) :=
    equiv.subst i_plus_one_plus_j⁻¹ (even.succ $ odd_plus_two h)
  with odd_plus_two : Π {n : ℕ}, odd n → odd (n + 2)
  | (n + 1) (odd.succ h) :=
    equiv.subst i_plus_one_plus_j⁻¹ (odd.succ $ even_plus_two h)

  def assoc_tetra {i j k l : ℕ} : i + (j + k) + l = (i + j) + (k + l) := calc
    (i + (j + k)) + l = i + ((j + k) + l) : by apply assoc
                  ... = i + (j + (k + l)) : begin apply eq.map, apply assoc end
                  ... = (i + j) + (k + l) : begin symmetry, apply assoc end

  mutual def even_plus_odd_is_odd, odd_plus_even_is_odd
  with even_plus_odd_is_odd : Π {n m : ℕ}, even n → odd m → odd (n + m)
  | 0 m even.zero h := equiv.subst (zero_plus_i m)⁻¹ h
  | (n + 1) (m + 1) (even.succ h) (odd.succ g) := begin
    apply equiv.subst (types.eq.symm $ i_plus_one_plus_j ⬝ assoc_tetra),
    apply odd_plus_two, apply odd_plus_even_is_odd h g
  end
  with odd_plus_even_is_odd : Π {n m : ℕ}, odd n → even m → odd (n + m)
  | n 0 h even.zero := h
  | (n + 1) (m + 1) (odd.succ h) (even.succ g) := begin
    apply equiv.subst (types.eq.symm $ i_plus_one_plus_j ⬝ assoc_tetra),
    apply odd_plus_two, apply even_plus_odd_is_odd h g
  end

  def n_plus_n (n : ℕ) : n * 2 = n + n :=
  begin apply eq.map (+ n), apply zero_plus_i end

  def sigma_to_even : Π {n : ℕ}, is_even n → even n
  | 0 _ := even.zero
  | (n + 1) ⟨m, h⟩ := equiv.subst (h ⬝ n_plus_n m)⁻¹
    (match parity m with
      | coproduct.inl g := even_plus_even_is_even g g
      | coproduct.inr g := odd_plus_odd_is_even g g
    end)

  def sigma_to_odd : Π {n : ℕ}, is_odd n → odd n
  | 0 ⟨m, h⟩ := not.absurd h⁻¹ ua.succ_neq_zero
  | (n + 1) ⟨m, h⟩ := begin
    apply odd.succ, apply sigma_to_even,
    existsi m, apply succ_inj, assumption
  end

  noncomputable def is_even_equiv {n : ℕ} : is_even n ≃ even n :=
  structures.prop_equiv_lemma (is_even_is_prop n) (even_is_prop n)
    sigma_to_even even_to_sigma

  noncomputable def is_odd_equiv {n : ℕ} : is_odd n ≃ odd n :=
  structures.prop_equiv_lemma (is_odd_is_prop n) (odd_is_prop n)
    sigma_to_odd odd_to_sigma

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