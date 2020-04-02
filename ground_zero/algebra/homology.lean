import ground_zero.algebra.group
open ground_zero.algebra (abelian) ground_zero.algebra.group

namespace ground_zero.algebra.homology
universe u

hott theory

structure chain_complex :=
(K : ℕ → Type u)
(is_group : Π n, abelian (K n))
(δ : Π n, K (n + 1) ⤳ K n)
(triv : Π n, δ n ⋅ δ (n + 1) = 0)

def B (C : chain_complex) :=
λ n, @ker (C.K (n + 1)) (C.is_group (n + 1)).to_group
          (C.K n)       (C.is_group n).to_group (C.δ n)

def Z (C : chain_complex) :=
λ n, @Im (C.K (n + 2)) (C.is_group (n + 2)).to_group
         (C.K (n + 1)) (C.is_group (n + 1)).to_group
         (C.δ (n + 1))

end ground_zero.algebra.homology