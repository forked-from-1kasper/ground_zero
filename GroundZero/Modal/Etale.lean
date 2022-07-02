import GroundZero.Theorems.Functions
import GroundZero.Modal.Disc

open GroundZero.Theorems.Functions
open GroundZero GroundZero.Types

namespace GroundZero.HITs.Infinitesimal
universe u v w

noncomputable section
  variable {A : Type u} {B : Type v} (f : A → B)

  hott def naturalitySquare : hcommSquare A (ℑ A) B (ℑ B) :=
  ⟨Im.ap f, ι, ι, f, Theorems.funext (Im.naturality f)⟩

  hott def etale := (naturalitySquare f).isPullback
  notation "étale" => etale
end

noncomputable def EtaleMap (A : Type u) (B : Type v) :=
Σ (f : A → B), étale f
infixr:70 " ─ét→ " => EtaleMap

noncomputable def SurjectiveEtaleMap (A : Type u) (B : Type v) :=
Σ (f : A → B), étale f × surjective f
infixr:70 " ─ét↠ " => SurjectiveEtaleMap

section
  variable (A : Type u) (B : Type v)

  instance : CoeFun (A ─ét→ B) (λ _, A → B) := ⟨Sigma.fst⟩
  instance : CoeFun (A ─ét↠ B) (λ _, A → B) := ⟨Sigma.fst⟩
end

noncomputable def isManifold (V : Type u) (M : Type v) :=
Σ (U : Type (max u v)), (U ─ét→ V) × (U ─ét↠ M)

noncomputable def Manifold (V : Type u) :=
Σ (M : Type v), isManifold V M

end GroundZero.HITs.Infinitesimal