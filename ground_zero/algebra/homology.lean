import ground_zero.algebra.group
open ground_zero ground_zero.algebra (abelian) ground_zero.algebra.group

namespace ground_zero.algebra.homology
universe u

hott theory

structure chain_complex :=
(K : ℕ → Type u)
(is_group : Π n, abelian (K n))
(δ : Π n, K (n + 1) ⤳ K n)
(triv : Π n, δ n ⋅ δ (n + 1) = 0)

def B (C : chain_complex) (n : ℕ) :=
@ker (C.K (n + 1)) (C.is_group (n + 1)).to_group
     (C.K n)       (C.is_group n).to_group (C.δ n)

def Z (C : chain_complex) (n : ℕ) :=
@Im (C.K (n + 2)) (C.is_group (n + 2)).to_group
    (C.K (n + 1)) (C.is_group (n + 1)).to_group
    (C.δ (n + 1))

instance (C : chain_complex) (n : ℕ) : algebra.group (Z C n) :=
let inst₁ := (C.is_group (n + 1)).to_group in
let inst₂ := (C.is_group (n + 2)).to_group in
@subgroup.is_group (C.K (n + 1)) (C.is_group (n + 1)).to_group
  (@im (C.K (n + 2)) inst₂
       (C.K (n + 1)) inst₁
       (C.δ (n + 1)))
  (@ground_zero.algebra.group.im_is_subgroup
       (C.K (n + 2)) inst₂
       (C.K (n + 1)) inst₁
       (C.δ (n + 1)))

end ground_zero.algebra.homology