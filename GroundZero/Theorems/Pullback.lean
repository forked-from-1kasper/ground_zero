import GroundZero.Theorems.Equiv
open GroundZero GroundZero.Types
open GroundZero.Structures
open HITs.Interval (happly)

namespace GroundZero.Theorems

section
  variable {P : Type k} {A : Type u} {B : Type v} {C : Type w} (η : hcommSquare P A B C)

  hott def terminalPullback : pullback (𝟏 → C) (λ f, η.right ∘ f) (λ g, η.bot ∘ g) ≃ pullback C η.right η.bot :=
  begin
    fapply Sigma.mk; { intro w; existsi (w.1.1 ★, w.1.2 ★); apply happly w.2 ★ }; apply Qinv.toBiinv;
    fapply Sigma.mk; { intro w; existsi (λ _, w.1.1, λ _, w.1.2); apply funext; intro; apply w.2 }; apply Prod.mk <;> intro w;
    { apply Id.map (Sigma.mk _); apply happly (happlyFunext _ _ _) };
    { apply Id.map (Sigma.mk _); transitivity;
      apply Id.map funext; change _ = happly w.2; apply funext;
      intro c; induction c; reflexivity; apply funextHapply }
  end
end

section
  variable {P : Type k} {A : Type u} {B : Type v} {C : Type w} (η : pullbackSquare P A B C)

  hott def pullbackCorner : P ≃ pullback C η.1.right η.1.bot :=
  begin
    apply Equiv.trans; apply Structures.terminalArrow;
    apply Equiv.trans; fapply Sigma.mk; exact η.1.induced 𝟏; apply η.2;
    apply terminalPullback
  end
end

end GroundZero.Theorems