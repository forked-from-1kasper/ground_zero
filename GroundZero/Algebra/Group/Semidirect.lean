import GroundZero.Algebra.Group.Automorphism

open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.Algebra

namespace Group
  -- Outer semidirect product
  hott def Semidirect {N H : Pregroup} [group N] [group H] (φ : H ⤳ Aut N) : Pregroup :=
  @Pregroup.intro (N.carrier × H.carrier) (prodHset N.hset H.hset)
    (λ (n₁, h₁) (n₂, h₂), (N.φ n₁ ((φ.fst h₁).fst n₂), H.φ h₁ h₂))
    (λ (n, h), ⟨(φ.1 (H.ι h)).1 (N.ι n), H.ι h⟩) (N.e, H.e)

  notation N " ⋊" "[" φ "] " H => Semidirect (N := N) (H := H) φ
  notation H " ⋉" "[" φ "] " N => Semidirect (N := N) (H := H) φ

  section
    variable {N H : Pregroup} [group N] [group H] (φ : H ⤳ Aut N)

    noncomputable instance Semidirect.semigroup : semigroup (N ⋊[φ] H).magma :=
    ⟨λ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩ ⟨n₃, h₃⟩, begin
      apply Product.prod;
      { transitivity; apply N.mulAssoc;
        apply Id.map (N.φ n₁); symmetry;
        transitivity; apply isoMul;
        apply Id.map; symmetry;
        transitivity; apply HITs.Interval.happly;
        apply Id.map; apply homoMul; reflexivity };
      { apply H.mulAssoc }
    end⟩

    noncomputable instance Semidirect.monoid : monoid (N ⋊[φ] H).premonoid :=
    ⟨Semidirect.semigroup φ, λ (n, h), begin
      apply Product.prod;
      { transitivity; apply N.oneMul;
        transitivity; apply HITs.Interval.happly;
        apply Id.map; apply homoUnit; reflexivity };
      { apply H.oneMul }
    end, λ (n, h), begin
      apply Product.prod;
      { transitivity; apply Id.map (N.φ n);
        apply isoUnit (φ.1 h); apply N.mulOne };
      { apply H.mulOne }
    end⟩

    noncomputable instance Semidirect.group : group (N ⋊[φ] H) :=
    ⟨Semidirect.monoid φ,
    λ ⟨n, h⟩, begin
      apply Product.prod;
      { transitivity; symmetry; apply isoMul;
        transitivity; apply Id.map;
        apply N.mulLeftInv; apply isoUnit };
      { apply H.mulLeftInv }
    end⟩
  end
end Group

end GroundZero.Algebra