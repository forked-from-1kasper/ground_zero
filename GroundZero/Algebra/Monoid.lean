import GroundZero.Algebra.Basic
import GroundZero.HITs.Trunc
open GroundZero GroundZero.Types

namespace GroundZero.Algebra

universe u v

namespace Monoid
  variable {M N : Premonoid}

  macro "setpi" : tactic =>
  `(intros; repeat { apply Structures.piRespectsNType 0; intros };
    apply Structures.hlevel.cumulative 0; apply HITs.Trunc.uniq 0)

  noncomputable hott def F.carrier (ε : Type u) : 0-Type :=
  ⟨∥List ε∥₀, HITs.Trunc.uniq 0⟩

  noncomputable hott def F (ε : Type u) : Premonoid :=
  begin
    existsi (F.carrier ε); apply Prod.mk;
    intro b; induction b using Bool.casesOn;
    { intro; exact HITs.Trunc.elem [] };
    { intro ⟨x, y, _⟩; apply HITs.Trunc.lift₂ List.append x y };
    { intro z; apply Proto.Empty.elim z }
  end
end Monoid

end GroundZero.Algebra