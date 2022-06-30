import GroundZero.Modal.Infinitesimal
open GroundZero.Types

namespace GroundZero.HITs.Infinitesimal
universe u v w

-- infinitesimally close
hott def infinitesimallyClose {A : Type u} (a b : A) := ι a = ι b
infix:80 " ~ " => infinitesimallyClose

hott def Disc {A : Type u} (a : A) := Σ b, a ~ b
notation "𝔻" => Disc

hott def discBundle (A : Type u) := Σ (a : A), 𝔻 a
notation "T∞" => discBundle

hott def center {A : Type u} (a : A) : 𝔻 a := ⟨a, idp (ι a)⟩

noncomputable section
  variable {A : Type u} {B : Type v} (f : A → B)

  hott def infProxAp {a b : A} : a ~ b → f a ~ f b :=
  λ ρ, (Im.naturality f a)⁻¹ ⬝ Id.ap (Im.ap f) ρ ⬝ Im.naturality f b

  hott def d (x : A) : 𝔻 x → 𝔻 (f x) :=
  λ ε, ⟨f ε.1, infProxAp f ε.2⟩

  hott def bundleAp : T∞ A → T∞ B :=
  λ τ, ⟨f τ.1, d f τ.1 τ.2⟩
end

end GroundZero.HITs.Infinitesimal