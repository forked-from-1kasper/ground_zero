import ground_zero.algebra.group
open ground_zero ground_zero.types ground_zero.algebra.group

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
  subgroup.group _ (ζ C n)

  abbreviation B (C : chain_complex) (n : ℕ) :=
  subgroup.inter (im (C.δ (n + 1)).fst) (ζ C n)

  instance (C : chain_complex) (n : ℕ) : Z C n ⊵ B C n :=
  group.abelian_subgroup_is_normal _ _

  noncomputable def H (C : chain_complex) (n : ℕ) :=
  (Z C n)\(B C n)
end homology

namespace digon
  open homology (B Z H)

  @[hott] noncomputable def K : ℕ → group
  |    0    := Z₁
  |    1    := FAb 𝟐 -- two points
  |    2    := FAb 𝟐 -- and two paths between them
  | (n + 3) := Z₁    -- and no higher-dimensional paths

  noncomputable instance K.abelian : Π n, abelian (K n)
  |    0    := by change abelian Z₁; apply_instance
  |    1    := by change abelian (FAb _); apply_instance
  |    2    := by change abelian (FAb _); apply_instance
  | (n + 3) := by change abelian Z₁; apply_instance

  noncomputable def δ : Π n, K (n + 1) ⤳ K n
  |    0    := 0
  |    1    :=
  FAb.homomorphism
    (λ x, match x with
    | ff := right_div (FAb.elem tt) (FAb.elem ff)
    | tt := right_div (FAb.elem ff) (FAb.elem tt)
    end)
  | (n + 2) := 0

  noncomputable def C : homology.chain_complex :=
  ⟨K, K.abelian, δ, begin
    intro n, apply homo.funext,
    intro x, induction n with n ih, reflexivity,
    { induction x, induction n; reflexivity }
  end⟩

  @[hott] noncomputable def imₙ.encode (n : ℕ) : B C (n + 1) ⊆ triv (Z C _) :=
  begin
    intro x, fapply HITs.merely.rec, apply ens.prop,
    intro p, induction p with y p,
    induction y, fapply types.sigma.prod,
    apply p, apply ens.prop
  end

  @[hott] noncomputable def imₙ.decode (n : ℕ) : triv (Z C _) ⊆ B C (n + 1) :=
  begin intros x p, induction p, apply HITs.merely.elem, existsi ★, trivial end

  @[hott] noncomputable def split (n : ℕ) := calc
    H C (n + 1) ≅ Z C (n + 1) \ triv (Z C _) : factor.iso (imₙ.encode n) (imₙ.decode n)
            ... ≅ Z C (n + 1)                : iso.symm group.triv.factor

  @[hott] noncomputable def ker_triv_is_univ (G H : group) :
    @ker G H 0 = ens.univ G.carrier :=
  begin
    apply ens.ext, intro x, split; intro p, { exact ★ },
    { change _ = _, reflexivity }
  end

  @[hott] noncomputable def Zₙ (n : ℕ) : Z C (n + 2) ≅ Z₁ :=
  begin
    apply types.equiv.transport (≅ Z₁), change subgroup.group (K _) (ens.univ _) = _,
    apply subgroup.ext.{0 0}, symmetry, apply ker_triv_is_univ,
    apply group.univ_is_subgroup, change _ ≅ _, symmetry, apply univ_iso
  end

  @[hott] noncomputable def Hₙ (n : ℕ) := calc
    H C (n + 2) ≅ Z C (n + 2) : split (n + 1)
            ... ≅ Z₁          : Zₙ n
end digon

end ground_zero.algebra