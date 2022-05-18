import ground_zero.cubical
open ground_zero.cubical

/-
  This example on Lean.
  https://tonpa.guru/stream/2017/2017-10-31%20Доказательство%20коммутативности%20в%20кубике.txt
-/

namespace ground_zero.cubical.cubicaltt

def add (m : ℕ) : ℕ → ℕ
|    0    := m
| (n + 1) := nat.succ (add n)

@[hott] def add_zero : Π a, Path ℕ (add nat.zero a) a
|    0    := <i> nat.zero
| (a + 1) := <i> nat.succ (add_zero a # i)

@[hott] def add_succ (a : ℕ) : Π b, Path ℕ (add (nat.succ a) b) (nat.succ (add a b))
|    0    := <i> nat.succ a
| (b + 1) := <i> nat.succ (add_succ b # i)

@[hott] def add_zero_inv : Π a, Path ℕ a (add a nat.zero) :=
Path.refl

@[hott] def add_comm (a : ℕ) : Π b, Path ℕ (add a b) (add b a)
|    0    := <i> (add_zero a) # −i
| (b + 1) := Path.kan
            (<i> nat.succ (add_comm b # i))
            (<j> nat.succ (add a b))
            (<j> add_succ b a # −j)

@[hott] def add_assoc (a b : ℕ) : Π c, Path ℕ (add a (add b c)) (add (add a b) c)
|    0    := <i> add a b
| (c + 1) := <i> nat.succ (add_assoc c # i)

@[hott] def add_comm₃ {a b c : ℕ} : Path ℕ (add a (add b c)) (add c (add b a) ):=
let r : Path ℕ (add a (add b c)) (add a (add c b)) :=
<i> add a (add_comm b c # i) in
Path.kan (add_comm a (add c b))
  (<j> r # −j) (<j> add_assoc c b a # −j)

@[hott] example (n m : ℕ) (h : Path ℕ n m) : Path ℕ (n + 1) (m + 1) :=
<i> nat.succ (h # i)

end ground_zero.cubical.cubicaltt