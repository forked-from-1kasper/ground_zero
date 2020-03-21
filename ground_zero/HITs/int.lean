import ground_zero.theorems.nat

/-
  Integers ℤ as a quotient of ℕ × ℕ.
  * HoTT 6.10, remark 6.10.7
-/

abbreviation builtin.int := int

hott theory

namespace ground_zero.HITs

def int.rel : ℕ × ℕ → ℕ × ℕ → Type
| ⟨a, b⟩ ⟨c, d⟩ := a + d = b + c

def int := graph int.rel
local notation ℤ := int

namespace nat.product
  universes u v

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
end nat.product

namespace int
  universes u v

  def mk : ℕ × ℕ → ℤ := graph.elem
  def elem (a b : ℕ) : ℤ := graph.elem (a, b)

  def pos (n : ℕ) := mk (n, 0)
  instance : has_coe ℕ ℤ := ⟨pos⟩

  def neg (n : ℕ) := mk (0, n)

  instance : has_zero int := ⟨mk (0, 0)⟩
  instance : has_one int  := ⟨mk (1, 0)⟩

  @[hott] def knife {a b c d : ℕ} (H : a + d = b + c :> ℕ) :
    mk (a, b) = mk (c, d) :> ℤ :=
  graph.line H

  @[hott] def ind {π : ℤ → Type u}
    (mk₁ : Π (x : ℕ × ℕ), π (mk x))
    (knife₁ : Π {a b c d : ℕ} (H : a + d = b + c),
      mk₁ (a, b) =[knife H] mk₁ (c, d)) (x : ℤ) : π x := begin
    fapply graph.ind, exact mk₁,
    { intros x y H, cases x with a b, cases y with c d, apply knife₁ }
  end

  @[hott] def rec {π : Type u}
    (mk₁ : ℕ × ℕ → π)
    (knife₁ : Π {a b c d : ℕ} (H : a + d = b + c),
      mk₁ (a, b) = mk₁ (c, d)) : ℤ → π := begin
    fapply graph.rec, exact mk₁,
    { intros x y H, cases x with a b, cases y with c d,
      apply knife₁, assumption }
  end

  @[hott] instance : has_neg int :=
  ⟨rec (λ x, mk ⟨x.pr₂, x.pr₁⟩)
    (begin intros a b c d H, apply knife, symmetry, assumption end)⟩

  @[hott] theorem k_equiv (a b k : ℕ) : mk (a, b) = mk (a + k, b + k) := begin
    apply knife, transitivity,
    { symmetry, apply ground_zero.theorems.nat.assoc },
    symmetry, transitivity, { symmetry, apply ground_zero.theorems.nat.assoc },
    apply ground_zero.types.eq.map (+ k), apply ground_zero.theorems.nat.comm
  end
end int

end ground_zero.HITs