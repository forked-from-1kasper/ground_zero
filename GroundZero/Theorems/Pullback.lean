import GroundZero.Theorems.Equiv
open GroundZero GroundZero.Types

namespace GroundZero.Theorems

section
  variable {P : Type k} {A : Type u} {B : Type v} {C : Type w}
           (η : pullbackSquare P A B C)

  hott def pullbackCorner : P ≃ pullback C η.1.right η.1.bot :=
  begin
    apply Equiv.trans; apply Equiv.symm; apply Structures.cozeroMorphismEqv;
    apply Equiv.trans; fapply Sigma.mk; exact η.1.induced 𝟏; apply η.2;
    apply Equiv.trans; apply Theorems.Equiv.respectsEquivOverFst;
    apply ua.productEquiv₃ <;> apply Structures.cozeroMorphismEqv;
    apply Sigma.respectsEquiv; intro ⟨a, b⟩;
    apply Equiv.trans; apply Theorems.full;
    apply Structures.familyOverUnit
  end
end

end GroundZero.Theorems