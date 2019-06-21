import ground_zero.algebra.group
open ground_zero.algebra (renaming group -> grp) ground_zero.algebra.group

hott theory

namespace ground_zero.algebra.homology

universes u

structure chain_complex :=
(K : ℕ → Type u) [is_group : Π n, grp (K n)] [commutes : Π n, abelian (K n)]
(d : Π n, K (nat.succ n) ⤳ K n)
(condition : Π n, d n ⋅ d (nat.succ n) = 0)
(B := λ n, Ker (d n))
(Z := λ n, im (d $ nat.succ n))

end ground_zero.algebra.homology