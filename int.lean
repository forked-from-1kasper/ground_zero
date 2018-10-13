import ground_zero.eq

namespace ground_zero

def int.rel : ℕ × ℕ → ℕ × ℕ → Prop
| (a, b) (c, d) := a + d = b + c

def int := quot int.rel
notation ℤ := int

namespace nat.product
  def add (x y : ℕ × ℕ) : ℕ × ℕ := begin
    cases x with a b, cases y with c d,
    split, apply a + c, apply b + d
  end
  instance : has_add (ℕ × ℕ) := ⟨add⟩

  def mul (x y : ℕ × ℕ) : ℕ × ℕ := begin
    cases x with a b, cases y with c d,
    split, apply a * c + b * d,
    apply a * d + b * c
  end
  instance : has_mul (ℕ × ℕ) := ⟨mul⟩

  lemma add_comm (x y : ℕ × ℕ) : x + y = y + x := begin
    cases x with a b, cases y with c d,
    simp [has_add.add], simp [add]
  end

  lemma mul_comm (x y : ℕ × ℕ) : x * y = y * x := begin
    cases x with a b, cases y with c d,
    simp [has_mul.mul], simp [mul],
    rw [nat.mul_comm c a], rw [nat.mul_comm d b],
    rw [nat.mul_comm c b], rw [nat.mul_comm d a],
    rw [nat.add_comm (b * c) (a * d)]
  end

  lemma rw.add (a b : ℕ × ℕ) : nat.product.add a b = a + b :=
  by trivial

  lemma rw.mul (a b : ℕ × ℕ) : nat.product.mul a b = a * b :=
  by trivial
end nat.product

namespace int

  def mk : ℕ × ℕ → int := quot.mk rel
  def pos (n : ℕ) := mk (n, 0)
  def neg (n : ℕ) := mk (0, n)

  instance : has_neg int :=
  ⟨quot.lift
    (λ (x : ℕ × ℕ), mk (x.snd, x.fst))
    (begin
      intros x y H, simp,
      cases x with a b,
      cases y with c d,
      simp, apply quot.sound,
      simp [rel], symmetry,
      assumption
    end)⟩

  lemma nat_rw (a b : ℕ) : nat.add a b = a + b :=
  by trivial

  def lift₂ (f : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ)
    (h₁ : Π (a b x : ℕ × ℕ) (H : rel a b), mk (f x a) = mk (f x b))
    (h₂ : Π (a b : ℕ × ℕ), mk (f a b) = mk (f b a))
    (x y : int) : int :=
  quot.lift
    (λ x, quot.lift
          (λ y, mk (f x y))
          (begin intros a b H, simp, apply h₁, assumption end) y)
    (begin
      intros a b H, simp,
      induction y, simp,
      rw [h₂ a y], rw [h₂ b y], apply h₁,
      assumption, trivial
    end) x

  lemma add_saves_int {a b c d : ℕ} (H : a + d = b + c)
    (y : ℕ × ℕ) :
    mk ((a, b) + y) = mk ((c, d) + y) := begin
    cases y with u v,
    simp [has_add.add],
    apply quot.sound, simp [nat.product.add], simp [rel],
    rw [←nat.add_assoc], rw [H],
    rw [nat.add_assoc]
  end

  def add : int → int → int := begin
    apply lift₂ nat.product.add,
    { intros x y u H,
      cases x with a b, cases y with c d,
      repeat { rw [nat.product.rw.add] },
      rw [nat.product.add_comm u (a, b)],
      rw [nat.product.add_comm u (c, d)],
      apply add_saves_int, assumption },
    { intros x y,
      apply eq.map mk,
      apply nat.product.add_comm }
  end

  instance : has_add int := ⟨add⟩
  instance : has_sub int := ⟨λ a b, a + (-b)⟩

  def mul : int → int → int := begin
    apply lift₂ nat.product.mul,
    { intros x y z H,
      cases x with a b, cases y with c d,
      cases z with u v, simp [nat.product.mul],
      apply quot.sound, simp [rel],
      rw [←nat.add_assoc (u * a)],
      rw [←nat.add_assoc (u * b)],

      rw [←nat.left_distrib u a d],
      rw [←nat.left_distrib v b c],

      rw [←nat.left_distrib u b c],
      rw [←nat.left_distrib v a d],
      
      simp [rel] at H, rw [H] },
    { intros x y,
      apply eq.map mk,
      apply nat.product.mul_comm }
  end
  instance : has_mul int := ⟨mul⟩

  theorem k_equiv (a b k : ℕ) : mk (a, b) = mk (a + k, b + k) :=
  begin apply quot.sound, simp [rel] end
end int

end ground_zero