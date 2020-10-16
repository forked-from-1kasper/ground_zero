import ground_zero.algebra.group
open ground_zero ground_zero.algebra (abelian) ground_zero.algebra.group

namespace ground_zero.algebra
universe u

hott theory

namespace homology
  structure chain_complex :=
  (K    : ℕ → group)
  (ab   : Π n, abelian (K n))
  (δ    : Π n, K (n + 1) ⤳ K n)
  (triv : Π n, δ n ⋅ δ (n + 1) = 0)

  instance (C : chain_complex) (n : ℕ) : abelian (C.K n) := C.ab n

  abbreviation ζ (C : chain_complex) (n : ℕ) :=
  ker (C.δ n)

  abbreviation Z (C : chain_complex) (n : ℕ) :=
  group.subgroup.group _ (ζ C n)

  abbreviation B (C : chain_complex) (n : ℕ) :=
  algebra.group.subgroup.inter (im (C.δ (n + 1)).fst) (ζ C n)

  instance (C : chain_complex) (n : ℕ) : Z C n ⊵ B C n :=
  group.abelian_subgroup_is_normal _ _

  noncomputable def H (C : chain_complex) (n : ℕ) :=
  (Z C n)\(B C n)
end homology

namespace digon
  open homology (B Z H)

  @[hott] noncomputable def K : ℕ → group
  |    0    := FAb 𝟐 -- two points
  |    1    := FAb 𝟐 -- and two paths between them
  | (n + 2) := Z₁    -- and no higher-dimensional paths

  noncomputable instance K.abelian : Π n, abelian (K n)
  |    0    := by change abelian (FAb _); apply_instance
  |    1    := by change abelian (FAb _); apply_instance
  | (n + 2) := by change abelian Z₁; apply_instance

  noncomputable def δ : Π n, K (n + 1) ⤳ K n
  |    0    :=
  FAb.homomorphism
    (λ x, match x with
    | ff := right_div (FAb.elem tt) (FAb.elem ff)
    | tt := right_div (FAb.elem ff) (FAb.elem tt)
    end)
  | (n + 1) := 0

  noncomputable def C : homology.chain_complex :=
  ⟨K, K.abelian, δ, begin
    intro n, apply homo.funext,
    intro x, induction x,
    induction n; reflexivity
  end⟩

  @[hott] noncomputable def imₙ.encode (n : ℕ) : B C n ⊆ triv (Z C n) :=
  begin
    intro x, fapply HITs.merely.rec, apply ens.prop,
    { intro p, induction p with y p,
      induction y, fapply types.sigma.prod,
      apply p, apply ens.prop }
  end

  @[hott] noncomputable def imₙ.decode (n : ℕ) : triv (Z C n) ⊆ B C n :=
  begin
    intros x p, induction p,
    apply HITs.merely.elem,
    existsi ★, reflexivity
  end

  @[hott] noncomputable def split (n : ℕ) : H C n ≅ Z C n := calc
    H C n ≅ Z C n \ triv (Z C n) : factor.iso (imₙ.encode n) (imₙ.decode n)
      ... ≅ Z C n                : iso.symm group.triv.factor
end digon

end ground_zero.algebra