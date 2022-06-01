import GroundZero.Cubical.V
open GroundZero.Cubical

/-
  This example on Lean.
  https://tonpa.guru/stream/2017/2017-10-31%20Доказательство%20коммутативности%20в%20кубике.txt
-/

namespace GroundZero.Cubical.Cubicaltt

hott def add (m : ℕ) : ℕ → ℕ
| Nat.zero   => m
| Nat.succ n => Nat.succ (add m n)

hott def addZero : Π a, Path ℕ (add Nat.zero a) a
| Nat.zero   => <_> Nat.zero
| Nat.succ a => <i> Nat.succ ((addZero a) @ i)

hott def addSucc (a : ℕ) : Π b, Path ℕ (add (Nat.succ a) b) (Nat.succ (add a b))
| Nat.zero   => <_> Nat.succ a
| Nat.succ b => <i> Nat.succ ((addSucc a b) @ i)

hott def addZeroInv : Π a, Path ℕ a (add a Nat.zero) :=
Path.refl

hott def addComm (a : ℕ) : Π b, Path ℕ (add a b) (add b a)
| Nat.zero   => <i> (addZero a) @ −i
| Nat.succ b => Path.kan (<i> Nat.succ ((addComm a b) @ i)) (<j> Nat.succ (add a b)) (<j> (addSucc b a) @ −j)

hott def addAssoc (a b : ℕ) : Π c, Path ℕ (add a (add b c)) (add (add a b) c)
| Nat.zero   => <_> add a b
| Nat.succ c => <i> Nat.succ ((addAssoc a b c) @ i)

hott def addComm₃ {a b c : ℕ} : Path ℕ (add a (add b c)) (add c (add b a) ):=
let r : Path ℕ (add a (add b c)) (add a (add c b)) :=
<i> add a ((addComm b c) @ i);
Path.kan (addComm a (add c b)) (<j> r @ −j) (<j> (addAssoc c b a) @ −j)

example (n m : ℕ) (h : Path ℕ n m) : Path ℕ (n + 1) (m + 1) :=
<i> Nat.succ (h @ i)

end GroundZero.Cubical.Cubicaltt