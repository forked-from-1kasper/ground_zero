import ground_zero.types.equiv

namespace ground_zero.types

/-
  +2 = pos 2
  +1 = pos 1
   0 = pos 0
  −1 = neg 0
  −2 = neg 1
-/
inductive integer
| pos : ℕ → integer
| neg : ℕ → integer
namespace integer

instance : has_zero integer := ⟨pos 0⟩
instance : has_one integer := ⟨pos 1⟩

instance : has_repr integer :=
⟨λ x, match x with
| (pos n) := to_string n
| (neg n) := "−" ++ to_string (n + 1)
end⟩

def negate : integer → integer
| (pos $ n + 1) := neg n
| (pos 0)       := pos 0
| (neg n)       := pos (n + 1)

instance : has_neg integer := ⟨negate⟩
instance : has_coe ℕ integer := ⟨integer.pos⟩

def auxsucc : ℕ → integer
| 0 := pos 0
| (n + 1) := neg n

def succ : integer → integer
| (neg u) := auxsucc u
| (pos v) := pos (v + 1)

def auxpred : ℕ → integer
| 0 := neg 0
| (n + 1) := pos n

def pred : integer → integer
| (neg u) := neg (u + 1)
| (pos v) := auxpred v

def succ_equiv : integer ≃ integer := begin
  existsi succ, split; existsi pred,
  repeat {
    intro n, induction n,
    repeat { trivial },
    { induction n with n ih,
      repeat { trivial } }
  }
end
end integer

end ground_zero.types