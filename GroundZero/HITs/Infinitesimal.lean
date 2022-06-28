import GroundZero.Types.Equiv
open GroundZero.Types.Equiv (biinv)

/-
  The modality of shape infinitesimal in cohesive infinity topos.
  https://github.com/forked-from-1kasper/anders/blob/master/library/modal/infinitesimal.anders

  * HoTT 7.7 Modalities
-/

namespace GroundZero.HITs.Infinitesimal
universe u v

axiom Im : Type u → Type u
notation "ℑ" => Im

axiom ι {A : Type u} : A → ℑ A

def isCoreduced (A : Type u) := biinv (@ι A)
axiom Im.coreduced (A : Type u) : isCoreduced (ℑ A)

axiom Im.ind {A : Type u} {B : ℑ A → Type v}
  (η : Π i, isCoreduced (B i)) (f : Π x, B (ι x)) : Π x, B x

axiom Im.ind.βrule {A : Type u} {B : ℑ A → Type v}
  (η : Π i, isCoreduced (B i)) (f : Π x, B (ι x)) :
  Π x, Im.ind η f (ι x) = f x

noncomputable section
  variable {A : Type u} {B : Type v} (η : isCoreduced B) (f : A → B)

  hott def Im.rec : Im A → B := Im.ind (λ _, η) f

  hott def Im.rec.βrule : Π x, Im.rec η f (ι x) = f x :=
  Im.ind.βrule (λ _, η) f
end

noncomputable hott def Im.app {A : Type u} {B : Type v}
  (f : A → B) : ℑ A → ℑ B :=
Im.rec (Im.coreduced B) (ι ∘ f)

noncomputable hott def Im.naturality {A : Type u} {B : Type v}
  (f : A → B) (x : A) : ι (f x) = Im.app f (ι x) :=
begin symmetry; apply Im.rec.βrule end

end GroundZero.HITs.Infinitesimal