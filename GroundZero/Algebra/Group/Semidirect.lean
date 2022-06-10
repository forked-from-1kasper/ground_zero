import GroundZero.Algebra.Group.Automorphism

open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.Algebra

namespace Group
  -- Outer semidirect product
  hott def Semidirect {N H : Group} (φ : Group.Hom H (Aut N)) : Group :=
  @Group.intro (N.carrier × H.carrier) (prodHset N.hset H.hset)
    (λ (n₁, h₁) (n₂, h₂), (N.φ n₁ ((φ.fst h₁).fst n₂), H.φ h₁ h₂))
    (λ (n, h), ⟨(φ.1 (H.ι h)).1 (N.ι n), H.ι h⟩) (N.e, H.e)
    (λ (n₁, h₁) (n₂, h₂) (n₃, h₃), begin
      apply Product.prod;
      { transitivity; apply N.mulAssoc;
        apply Id.map (N.φ n₁); symmetry;
        transitivity; apply isoMul;
        apply Id.map; symmetry;
        transitivity; apply HITs.Interval.happly;
        apply Id.map; apply homoMul; reflexivity };
      { apply H.mulAssoc }
    end)
    (λ (n, h), begin
      apply Product.prod;
      { transitivity; apply N.oneMul;
        transitivity; apply HITs.Interval.happly;
        apply Id.map; apply homoUnit; reflexivity };
      { apply H.oneMul }
    end)
    (λ (n, h), begin
      apply Product.prod;
      { transitivity; apply Id.map (N.φ n);
        apply isoUnit (φ.1 h); apply N.mulOne };
      { apply H.mulOne }
    end)
    (λ ⟨n, h⟩, begin
      apply Product.prod;
      { transitivity; symmetry; apply isoMul;
        transitivity; apply Id.map;
        apply N.mulLeftInv; apply isoUnit };
      { apply H.mulLeftInv }
    end)

  notation N " ⋊" "[" φ "] " H => Semidirect (N := N) (H := H) φ
  notation H " ⋉" "[" φ "] " N => Semidirect (N := N) (H := H) φ
end Group

end GroundZero.Algebra