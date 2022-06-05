import GroundZero.Algebra.Group.Product
import GroundZero.Algebra.Group.Factor
import GroundZero.Algebra.Group.Z

open GroundZero.HITs GroundZero.Algebra.Group
open GroundZero GroundZero.Types

namespace GroundZero.Algebra
universe u

namespace Homology
  structure Chain :=
  (K    : ℕ → Pregroup)
  (ab   : Π n, abelian (K n))
  (δ    : Π n, K (n + 1) ⤳ K n)
  (triv : Π n, δ n ⋅ δ (n + 1) = 0)

  instance (C : Chain) (n : ℕ) : abelian (C.K n) := C.ab n

  def δ {C : Chain} (n : ℕ) : (C.K (n + 1)).carrier → (C.K n).carrier :=
  (C.δ n).1

  def triv (C : Chain) (n : ℕ) : Π x, δ n (δ (n + 1) x) = (C.K n).e :=
  HITs.Interval.happly (Id.map Sigma.fst (C.triv n))

  abbrev ζ (C : Chain) (n : ℕ) := ker (C.δ n)
  abbrev Z (C : Chain) (n : ℕ) := Subgroup _ (ζ C n)
  abbrev B (C : Chain) (n : ℕ) := Group.inter (Group.im (C.δ (n + 1))) (ζ C n)

  instance (C : Chain) (n : ℕ) : Z C n ⊵ B C n :=
  Group.abelianSubgroupIsNormal _ _

  noncomputable hott def H (C : Chain) (n : ℕ) :=
  (Z C n)\(B C n)
end Homology

section
  variable (G H : Pregroup) [Algebra.group G] [abelian H]

  noncomputable hott def Hom : Pregroup :=
  begin
    fapply @Pregroup.intro (G ⤳ H) Algebra.Homo.hset;
    { intros φ ψ; fapply Group.mkhomo;
      { intro x; exact H.φ (φ.fst x) (ψ.fst x) };
      { intros a b; transitivity;
        fapply Equiv.bimap H.φ <;> apply homoMul;
        transitivity; apply H.mulAssoc;
        transitivity; apply Id.map (H.φ (φ.1 a));
        transitivity; apply H.mulComm; apply H.mulAssoc;
        transitivity; symmetry; apply H.mulAssoc;
        apply Id.map; apply H.mulComm } };
    { intro φ; fapply Group.mkhomo;
      { exact H.ι ∘ φ.1 };
      { intros a b; transitivity; apply Id.map H.ι; apply homoMul;
        transitivity; apply invExplode; apply H.mulComm } };
    exact Homo.zero
  end

  noncomputable instance Hom.semigroup : semigroup (Hom G H).magma :=
  begin constructor; intros a b c; fapply Homo.funext; intro; apply H.mulAssoc end

  noncomputable instance Hom.monoid : monoid (Hom G H).premonoid :=
  begin
    constructor; exact Hom.semigroup G H;
    { intro φ; fapply Homo.funext; intro; apply H.oneMul };
    { intro φ; fapply Homo.funext; intro; apply H.mulOne }
  end

  noncomputable instance Hom.group : group (Hom G H) :=
  begin
    constructor; exact Hom.monoid G H; intro φ;
    fapply Homo.funext; intro; apply H.mulLeftInv
  end

  noncomputable instance Hom.abelian : abelian (Hom G H) :=
  begin constructor; intros a b; fapply Homo.funext; intro; apply H.mulComm end
end

namespace Cohomology
  open Homology (Chain)

  noncomputable hott def Cochain (C : Chain) (G : Pregroup) [abelian G] (n : ℕ) := Hom (C.K n) G

  variable (C : Chain) (G : Pregroup) [abelian G]

  noncomputable instance Cochain.group (n : ℕ) : group (Cochain C G n) := Hom.group _ _

  -- how?
  -- (deterministic) timeout at 'isDefEq', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

/-
  noncomputable hott def δ (k : ℕ) : Cochain C G k ⤳ Cochain C G (k + 1) :=
  begin
    fapply Group.mkhomo;
    { intro φ; fapply Group.mkhomo;
      { exact φ.1 ∘ (C.δ k).1 };
      { intros a b; transitivity; apply Id.map φ.1;
        apply homoMul; apply homoMul } };
    { intros φ ψ; fapply Homo.funext; intro; apply idp }
  end

  noncomputable hott def δ.triv (k : ℕ) : δ C G (k + 1) ⋅ δ C G k = 0 :=
  begin
    fapply Homo.funext; intro φ;
    fapply Homo.funext; intro;
    transitivity; apply Id.map φ.1;
    apply Homology.triv; apply homoUnit
  end

  noncomputable hott def ζ (k : ℕ) :=
  ker (δ C G (k + 1))

  noncomputable hott def Z (k : ℕ) :=
  Subgroup _ (ζ C G k)

  noncomputable instance (k : ℕ) : abelian (Z C G k) :=
  @Group.abelianSubgroupIsAbelian (Cochain C G (k + 1)) (Homo.abelian _ _) _

  noncomputable hott def B (k : ℕ) :=
  Group.inter (Group.im (δ C G k)) (ζ C G k)

  noncomputable instance (k : ℕ) : Z C G k ⊵ B C G k :=
  Group.abelianSubgroupIsNormal _ _

  noncomputable hott def H (k : ℕ) :=
  (Z C G k)\(B C G k)
-/
end Cohomology

namespace Digon
  open Homology (B Z H)

  notation "ZΩ²" => Group.Prod ZΩ ZΩ
end Digon

end GroundZero.Algebra