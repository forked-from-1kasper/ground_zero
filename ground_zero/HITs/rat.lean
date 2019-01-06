import ground_zero.HITs.int

local notation ℤ := ground_zero.HITs.int

namespace ground_zero.HITs

def rat.rel : ℤ × ℕ → ℤ × ℕ → Prop
| ⟨u, a⟩ ⟨v, b⟩ := u * int.pos (b + 1) = v * int.pos (a + 1)

def rat := quot rat.rel
notation `ℚ` := rat

namespace rat
  namespace product
    def add : ℤ × ℕ → ℤ × ℕ → ℤ × ℕ
    | ⟨u, a⟩ ⟨v, b⟩ := ⟨u * int.pos b + v * int.pos a, a * b⟩

    def mul : ℤ × ℕ → ℤ × ℕ → ℤ × ℕ
    | ⟨u, a⟩ ⟨v, b⟩ := ⟨u * v, a * b⟩
  end product
end rat

end ground_zero.HITs