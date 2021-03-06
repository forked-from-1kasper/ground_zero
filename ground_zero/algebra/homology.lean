import ground_zero.algebra.Z
open ground_zero.HITs ground_zero.algebra.group
open ground_zero ground_zero.types

namespace ground_zero.algebra
universe u

hott theory

namespace homology
  structure chain_complex :=
  (K    : ℕ → pregroup)
  (ab   : Π n, abelian (K n))
  (δ    : Π n, K (n + 1) ⤳ K n)
  (triv : Π n, δ n ⋅ δ (n + 1) = 0)

  instance (C : chain_complex) (n : ℕ) : abelian (C.K n) := C.ab n

  abbreviation ζ (C : chain_complex) (n : ℕ) :=
  ker (C.δ n)

  abbreviation Z (C : chain_complex) (n : ℕ) :=
  Subgroup _ (ζ C n)

  abbreviation B (C : chain_complex) (n : ℕ) :=
  group.inter (group.im (C.δ (n + 1))) (ζ C n)

  instance (C : chain_complex) (n : ℕ) : Z C n ⊵ B C n :=
  group.abelian_subgroup_is_normal _ _

  noncomputable def H (C : chain_complex) (n : ℕ) :=
  (Z C n)\(B C n)
end homology

namespace digon
  open homology (B Z H)

  notation `ZΩ²` := group.prod.{0 0} ZΩ ZΩ

  @[hott] noncomputable def K : ℕ → pregroup.{0}
  |    0    := Z₁
  |    1    := ZΩ² -- two points
  |    2    := ZΩ² -- and two paths between them
  | (n + 3) := Z₁  -- and no higher-dimensional paths

  noncomputable instance K.abelian : Π n, abelian (K n)
  |    0    := by change abelian Z₁;  apply_instance
  |    1    := by change abelian ZΩ²; apply_instance
  |    2    := by change abelian ZΩ²; apply_instance
  | (n + 3) := by change abelian Z₁;  apply_instance

  noncomputable def δ : Π n, K (n + 1) ⤳ K n
  |    0    := 0
  |    1    :=
  homo.prod (ZΩ.rec (circle.loop⁻¹, circle.loop))
            (ZΩ.rec (circle.loop, circle.loop⁻¹))
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

  @[hott] noncomputable def ker_triv_is_univ (G H : pregroup)
    [g : group G] [h : group H] : @ker G g H h 0 = group.univ G :=
  begin
    apply subgroup.ext, apply ens.ext,
    intro x, split; intro p, { exact ★ },
    { change _ = _, reflexivity }
  end

  @[hott] noncomputable def Zₙ (n : ℕ) : Z C (n + 2) ≅ Z₁ :=
  begin
    apply types.equiv.transport (≅ Z₁), change Subgroup (K _) (group.univ _) = _,
    apply Id.map (Subgroup _), symmetry, apply ker_triv_is_univ,
    change _ ≅ _, symmetry, apply univ_iso
  end

  @[hott] noncomputable def Hₙ (n : ℕ) := calc
    H C (n + 2) ≅ Z C (n + 2) : split (n + 1)
            ... ≅ Z₁          : Zₙ n
end digon

end ground_zero.algebra