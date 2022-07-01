import GroundZero.Modal.Disc
open GroundZero GroundZero.Types

namespace GroundZero.HITs.Infinitesimal
universe u v w

noncomputable section
  variable {A : Type u} {B : Type v} (f : A → B)

  hott def naturalitySquare : hcommSquare A (ℑ A) B (ℑ B) :=
  ⟨Im.ap f, ι, ι, f, Theorems.funext (Im.naturality f)⟩

  hott def isEtale := (naturalitySquare f).isPullback
  notation "isÉtale" => isEtale
end

noncomputable def EtaleMap (A : Type u) (B : Type v) :=
Σ (f : A → B), isEtale f
infixr:70 " ─ét→ " => EtaleMap

instance (A : Type u) (B : Type v) : CoeFun (A ─ét→ B) (λ _, A → B) := ⟨Sigma.fst⟩

end GroundZero.HITs.Infinitesimal