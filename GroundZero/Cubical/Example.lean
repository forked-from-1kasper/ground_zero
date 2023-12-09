import GroundZero.Cubical.V

open GroundZero.Cubical.Path (kan refl)
open GroundZero.Cubical

/-
  This example on Lean.
  https://github.com/mortberg/cubicaltt/blob/9baa6f2491cc61dbd4fd81d58323c04100381451/examples/nat.ctt#L52-L57
-/

namespace GroundZero.Cubical.Cubicaltt
open Nat (zero succ)

hott definition add (m : ℕ) : ℕ → ℕ
| zero   => m
| succ n => succ (add m n)

hott definition addZero : Π a, Path ℕ (add zero a) a
| zero   => <_> zero
| succ a => <i> succ ((addZero a) @ i)

hott definition addSucc (a : ℕ) : Π b, Path ℕ (add (succ a) b) (succ (add a b))
| zero   => <_> succ a
| succ b => <i> succ ((addSucc a b) @ i)

hott definition addZeroInv : Π a, Path ℕ a (add a zero) :=
refl

hott definition addComm (a : ℕ) : Π b, Path ℕ (add a b) (add b a)
| zero   => <i> (addZero a) @ −i
| succ b => kan (<i> succ ((addComm a b) @ i)) (<j> succ (add a b)) (<j> (addSucc b a) @ −j)

hott definition addAssoc (a b : ℕ) : Π c, Path ℕ (add a (add b c)) (add (add a b) c)
| zero   => <_> add a b
| succ c => <i> succ ((addAssoc a b c) @ i)

hott definition addComm₃ {a b c : ℕ} : Path ℕ (add a (add b c)) (add c (add b a) ):=
let r : Path ℕ (add a (add b c)) (add a (add c b)) :=
<i> add a ((addComm b c) @ i);
kan (addComm a (add c b)) (<j> r @ −j) (<j> (addAssoc c b a) @ −j)

hott example (n m : ℕ) (h : Path ℕ n m) : Path ℕ (n + 1) (m + 1) :=
<i> succ (h @ i)

end GroundZero.Cubical.Cubicaltt
