import ground_zero.algebra.Z
open ground_zero.HITs ground_zero.algebra.group
open ground_zero ground_zero.types

namespace ground_zero.algebra
universe u

hott theory

namespace homology
  structure chain :=
  (K    : ℕ → pregroup)
  (ab   : Π n, abelian (K n))
  (δ    : Π n, K (n + 1) ⤳ K n)
  (triv : Π n, δ n ⋅ δ (n + 1) = 0)

  instance (C : chain) (n : ℕ) : abelian (C.K n) := C.ab n

  def δ {C : chain} (n : ℕ) : (C.K (n + 1)).carrier → (C.K n).carrier :=
  (C.δ n).fst

  def triv (C : chain) (n : ℕ) : Π x, δ n (δ (n + 1) x) = (C.K n).e :=
  HITs.interval.happly (sigma.fst # (C.triv n))

  abbreviation ζ (C : chain) (n : ℕ) :=
  ker (C.δ n)

  abbreviation Z (C : chain) (n : ℕ) :=
  Subgroup _ (ζ C n)

  abbreviation B (C : chain) (n : ℕ) :=
  group.inter (group.im (C.δ (n + 1))) (ζ C n)

  instance (C : chain) (n : ℕ) : Z C n ⊵ B C n :=
  group.abelian_subgroup_is_normal _ _

  noncomputable def H (C : chain) (n : ℕ) :=
  (Z C n)\(B C n)
end homology

section
  variables (G H : pregroup) [group G] [abelian H]
  include G H

  @[hott] noncomputable def Homo : pregroup :=
  begin
    fapply @pregroup.intro (G ⤳ H) (λ _ _, algebra.homo.hset),
    { intros φ ψ, fapply group.mkhomo,
      { intro x, exact H.φ (φ.fst x) (ψ.fst x) },
      { intros a b, transitivity,
        fapply equiv.bimap H.φ; apply homo_mul,
        transitivity, apply H.mul_assoc,
        transitivity, apply Id.map (H.φ (φ.fst a)),
        transitivity, apply H.mul_comm, apply H.mul_assoc,
        transitivity, symmetry, apply H.mul_assoc,
        apply Id.map, apply H.mul_comm } },
    { intro φ, fapply group.mkhomo,
      { exact H.ι ∘ φ.fst },
      { intros a b, transitivity, apply Id.map H.ι, apply homo_mul,
        transitivity, apply inv_explode, apply H.mul_comm } },
    exact homo.zero
  end

  @[hott] noncomputable instance Homo.semigroup : semigroup (Homo G H).magma :=
  begin split, intros a b c, fapply homo.funext, intro x, apply H.mul_assoc end

  @[hott] noncomputable instance Homo.monoid : monoid (Homo G H).premonoid :=
  begin
    split, exact Homo.semigroup G H,
    all_goals
      { intro φ, fapply homo.funext, intro x,
        apply H.one_mul <|> apply H.mul_one }
  end

  @[hott] noncomputable instance Homo.group : group (Homo G H) :=
  begin
    split, exact Homo.monoid G H, intro φ,
    fapply homo.funext, intro x, apply H.mul_left_inv
  end

  @[hott] noncomputable instance Homo.abelian : abelian (Homo G H) :=
  begin split, intros a b, fapply homo.funext, intro x, apply H.mul_comm end
end

namespace cohomology
  open homology (chain)

  noncomputable def cochain (C : chain) (G : pregroup) [abelian G] (n : ℕ) :=
  Homo (C.K n) G

  variables (C : chain) (G : pregroup) [abelian G]

  noncomputable instance cochain.group (n : ℕ) : group (cochain C G n) :=
  by apply Homo.group

  @[hott] noncomputable def δ (k : ℕ) : cochain C G k ⤳ cochain C G (k + 1) :=
  begin
    fapply group.mkhomo,
    { intro φ, fapply group.mkhomo,
      { exact φ.fst ∘ (C.δ k).fst },
      { intros a b, transitivity,
        apply Id.map φ.fst, apply homo_mul,
        apply homo_mul } },
    { intros φ ψ, fapply homo.funext, reflexivity }
  end

  @[hott] noncomputable def δ.triv (k : ℕ) : δ C G (k + 1) ⋅ δ C G k = 0 :=
  begin
    fapply homo.funext, intro φ,
    fapply homo.funext, intro x,
    transitivity, apply Id.map φ.fst,
    apply homology.triv, apply homo_unit
  end

  noncomputable def ζ (k : ℕ) :=
  ker (δ C G (k + 1))

  noncomputable def Z (k : ℕ) :=
  Subgroup _ (ζ C G k)

  noncomputable instance (k : ℕ) : abelian (Z C G k) :=
  @group.abelian_subgroup_is_abelian (cochain C G (k + 1)) (Homo.abelian _ _) _

  noncomputable def B (k : ℕ) :=
  group.inter (group.im (δ C G k)) (ζ C G k)

  noncomputable instance (k : ℕ) : Z C G k ⊵ B C G k :=
  group.abelian_subgroup_is_normal _ _

  noncomputable def H (k : ℕ) :=
  (Z C G k)\(B C G k)
end cohomology

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

  noncomputable def C : homology.chain :=
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