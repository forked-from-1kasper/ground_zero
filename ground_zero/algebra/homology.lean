import ground_zero.algebra.group
open ground_zero ground_zero.algebra (abelian) ground_zero.algebra.group

namespace ground_zero.algebra.homology
universe u

hott theory

structure chain_complex :=
(K : ℕ → Type u)
(is_abelian : Π n, abelian (K n))
(δ : Π n, K (n + 1) ⤳ K n)
(triv : Π n, δ n ⋅ δ (n + 1) = 0)

def chain_complex.is_group (C : chain_complex) :
  Π n, algebra.group (C.K n) :=
λ n, (C.is_abelian n).to_group

instance chain_complex.groups (C : chain_complex) (n : ℕ) : algebra.group (C.K n) :=
chain_complex.is_group C n

abbreviation ζ (C : chain_complex) (n : ℕ) :=
im (C.δ (n + 1))

abbreviation Z (C : chain_complex) (n : ℕ) :=
(ζ C n).subtype

instance Z_is_group (C : chain_complex) (n : ℕ) : algebra.group (Z C n) :=
subgroup.is_group

abbreviation B (C : chain_complex) (n : ℕ) :=
ker (C.δ n ⋅ homo.surj (ζ C n))

def H (C : chain_complex) (n : ℕ) :=
(Z C n)/(B C n)

end ground_zero.algebra.homology