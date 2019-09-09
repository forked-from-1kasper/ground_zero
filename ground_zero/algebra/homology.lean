import ground_zero.algebra.group
open ground_zero.algebra (renaming group -> grp) ground_zero.algebra.group

hott theory

namespace ground_zero.algebra.homology

universes u

structure chain_complex :=
(K : ℕ → Type u)
(is_group : Π n, grp (K n))
(commutes : Π n, abelian (K n))
(d : Π n, K (nat.succ n) ⤳ K n)
(condition : Π n, d n ⋅ d (nat.succ n) = 0)

def B (C : chain_complex) :=
λ n, @ker _ _ (C.is_group (nat.succ n)) (C.is_group n) (C.d n)

def Z (C : chain_complex) :=
λ n, @Im _ _
  (C.is_group (nat.succ (nat.succ n)))
  (C.is_group (nat.succ n))
  (C.d (nat.succ n))

end ground_zero.algebra.homology