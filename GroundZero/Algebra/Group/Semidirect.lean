import GroundZero.Algebra.Group.Automorphism

open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.Algebra

namespace Group
  -- Outer semidirect product
  hott definition Semidirect {N H : Group} (φ : Hom H (Aut N)) : Group :=
  @Group.intro (N.carrier × H.carrier) (prodHset N.hset H.hset)
    (λ (n₁, h₁) (n₂, h₂), (N.φ n₁ ((φ.fst h₁).fst n₂), H.φ h₁ h₂))
    (λ (n, h), ⟨(φ.1 (H.ι h)).1 (N.ι n), H.ι h⟩) (N.e, H.e)
    (λ (n₁, h₁) (n₂, h₂) (n₃, h₃), begin
      apply Product.prod;
      { transitivity; apply N.mulAssoc;
        apply ap (N.φ n₁); symmetry;
        transitivity; apply isoMul;
        apply ap; symmetry;
        transitivity; apply HITs.Interval.happly;
        apply ap; apply homoMul; reflexivity };
      { apply H.mulAssoc }
    end)
    (λ (n, h), begin
      apply Product.prod;
      { transitivity; apply N.oneMul;
        transitivity; apply HITs.Interval.happly;
        apply ap; apply homoUnit; reflexivity };
      { apply H.oneMul }
    end)
    (λ ⟨n, h⟩, begin
      apply Product.prod;
      { transitivity; symmetry; apply isoMul;
        transitivity; apply ap;
        apply N.mulLeftInv; apply isoUnit };
      { apply H.mulLeftInv }
    end)

  notation N " ⋊" "[" φ "] " H => Semidirect (N := N) (H := H) φ
  notation H " ⋉" "[" φ "] " N => Semidirect (N := N) (H := H) φ
end Group

end GroundZero.Algebra
