namespace ground_zero

def int.rel : ℕ × ℕ → ℕ × ℕ → Prop
| (a, b) (c, d) := a + d = b + c

def int := quot int.rel
notation ℤ := int

namespace int
  def mk := quot.mk rel
  def pos (n : ℕ) := int.mk (n, 0)
  def neg (n : ℕ) := int.mk (0, n)

  instance nat_of_nat_add : has_add (ℕ × ℕ) :=
  ⟨begin
    intros x y,
    cases x with a b, cases y with c d,
    split, apply a + c, apply b + d
  end⟩

  lemma nat_rw (a b : ℕ) : nat.add a b = a + b :=
  by trivial

  lemma pair_add_comm (x y : ℕ × ℕ) : x + y = y + x := begin
    cases x with a b, cases y with c d,
    simp [has_add.add], repeat { rw [nat_rw] },
    rw [nat.add_comm a c], rw [nat.add_comm b d]
  end

  lemma add_saves_int {a b c d : ℕ} (H : a + d = b + c)
    (y : ℕ × ℕ) :
    mk ((a, b) + y) = mk ((c, d) + y) := begin
    cases y with u v,
    simp [has_add.add],
    apply quot.sound, simp [rel],
    repeat { rw [nat_rw] },
    rw [nat.add_comm a u], rw [nat.add_assoc],
    rw [←nat.add_assoc a d v],
    rw [H], rw [nat.add_assoc],
    rw [nat.add_comm c v], rw [←nat.add_assoc],
    rw [nat.add_assoc], rw [nat.add_comm],
    rw [nat.add_assoc b], rw [nat.add_assoc v],
    rw [nat.add_assoc b]
  end

  def add (x y : int) : int :=
  @quot.lift (ℕ × ℕ) rel int
    (λ x, quot.lift
      (λ y, mk (x + y))
      (begin
        intros x y H,
        cases x with a b, cases y with c d,
        simp [rel] at H,
        simp,
        rw [pair_add_comm x (a, b)],
        rw [pair_add_comm x (c, d)],
        apply add_saves_int,
        assumption
      end) y)
    (begin
      intros x y H,
      cases x with a b,
      cases y with c d,
      simp, simp [rel] at H,
      induction y, simp,
      apply add_saves_int,
      assumption, trivial
    end) x
  instance : has_add int := ⟨add⟩
end int

end ground_zero