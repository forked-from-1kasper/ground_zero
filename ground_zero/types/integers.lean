import ground_zero.types.equiv

namespace ground_zero.types

/-
  +2 = pos 2
  +1 = pos 1
   0 = pos 0
  −1 = neg 0
  −2 = neg 1
-/
inductive integers
| pos : ℕ → integers
| neg : ℕ → integers
namespace integers

instance : has_zero integers := ⟨pos 0⟩
instance : has_one integers := ⟨pos 1⟩

instance : has_repr integers :=
⟨λ x, match x with
| (pos n) := to_string n
| (neg n) := "−" ++ to_string (n + 1)
end⟩

def auxsucc : ℕ → integers
| 0 := pos 0
| (n + 1) := neg n

def succ : integers → integers
| (neg u) := auxsucc u
| (pos v) := pos (v + 1)

def auxpred : ℕ → integers
| 0 := neg 0
| (n + 1) := pos n

def pred : integers → integers
| (neg u) := neg (u + 1)
| (pos v) := auxpred v

def succ_equiv : integers ≃ integers := begin
  existsi succ, split; existsi pred,
  repeat {
    intro n, induction n,
    repeat { trivial },
    { induction n with n ih,
      repeat { trivial } }
  }
end
end integers

end ground_zero.types