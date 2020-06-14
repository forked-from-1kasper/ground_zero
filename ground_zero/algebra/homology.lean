import ground_zero.algebra.group
open ground_zero ground_zero.algebra (abelian) ground_zero.algebra.group

namespace ground_zero.algebra
universe u

hott theory

namespace homology
  structure chain_complex :=
  (K : ℕ → Type u)
  (is_abelian : Π n, abelian (K n))
  (δ : Π n, K (n + 1) ⤳ K n)
  (triv : Π n, δ n ⋅ δ (n + 1) = 0)

  instance chain_complex.abelian (C : chain_complex) (n : ℕ) : abelian (C.K n) :=
  C.is_abelian n

  abbreviation ζ (C : chain_complex) (n : ℕ) :=
  ker (C.δ n)

  abbreviation Z (C : chain_complex) (n : ℕ) :=
  (ζ C n).subtype

  abbreviation B (C : chain_complex) (n : ℕ) :=
  algebra.group.subgroup.inter (im (C.δ (n + 1)).fst) (ζ C n)

  def H (C : chain_complex) (n : ℕ) :=
  (Z C n)/(B C n)
end homology

namespace digon
  def K : ℕ → Type
  | 0 := FAb 𝟐 -- two points
  | 1 := FAb 𝟐 -- and two paths between them
  | _ := 𝟏     -- and no higher-dimensional paths

  noncomputable instance K.abelian : Π n, abelian (K n)
  |    0    := by apply FAb.abelian
  |    1    := by apply FAb.abelian
  | (n + 2) := by apply group.unit_is_abelian

  noncomputable def δ : Π n, K (n + 1) ⤳ K n
  |    0    :=
  FAb.homomorphism
    (λ x, match x with
    | ff := FAb.elem tt / FAb.elem ff
    | tt := FAb.elem ff / FAb.elem tt
    end)
  | (n + 1) := 0

  noncomputable def C : homology.chain_complex :=
  ⟨K, K.abelian, δ, begin
    intro n, apply homo.funext,
    intro x, induction x,
    induction n; reflexivity
  end⟩
end digon

end ground_zero.algebra