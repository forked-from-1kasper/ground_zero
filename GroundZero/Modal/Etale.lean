import GroundZero.Theorems.Functions
import GroundZero.Modal.Disc

open GroundZero.Theorems.Functions
open GroundZero GroundZero.Types
open GroundZero.Proto

namespace GroundZero.HITs.Infinitesimal
universe u v w

section
  variable {A : Type u} {B : Type v} (f : A → B)

  hott definition naturalitySquare : hcommSquare A (ℑ A) B (ℑ B) :=
  ⟨Im.ap f, ι, ι, f, Theorems.funext (Im.naturality f)⟩

  hott definition etale := (naturalitySquare f).isPullback
  notation "étale" => etale
end

section
  hott definition EtaleMap (A : Type u) (B : Type v) :=
  Σ (f : A → B), étale f
  infixr:70 " ─ét→ " => EtaleMap

  hott definition SurjectiveEtaleMap (A : Type u) (B : Type v) :=
  Σ (f : A → B), étale f × surjective f
  infixr:70 " ─ét↠ " => SurjectiveEtaleMap
end

section
  variable (A : Type u) (B : Type v)

  instance : CoeFun (A ─ét→ B) (λ _, A → B) := ⟨Sigma.fst⟩
  instance : CoeFun (A ─ét↠ B) (λ _, A → B) := ⟨Sigma.fst⟩
end

section
  hott definition isManifold (V : Type u) (M : Type v) :=
  Σ (U : Type (max u v)), (U ─ét→ V) × (U ─ét↠ M)

  hott definition Manifold (V : Type u) :=
  Σ (M : Type v), isManifold V M
end

end GroundZero.HITs.Infinitesimal
