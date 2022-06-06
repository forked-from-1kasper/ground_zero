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
axiom Im.unit {A : Type u} : A → Im A

def isCoreduced (A : Type u) := biinv (@Im.unit A)
axiom Im.coreduced (A : Type u) : isCoreduced (Im A)

axiom Im.ind {A : Type u} {B : Im A → Type v}
  (h : Π i, isCoreduced (B i)) (f : Π x, B (Im.unit x)) : Π x, B x

axiom Im.ind.βrule {A : Type u} {B : Im A → Type v}
  (h : Π i, isCoreduced (B i)) (f : Π x, B (Im.unit x)) :
  Π x, Im.ind h f (Im.unit x) = f x

noncomputable hott def Im.rec {A : Type u} {B : Type v}
  (h : isCoreduced B) (f : A → B) : Im A → B :=
Im.ind (λ _, h) f

noncomputable hott def Im.rec.βrule {A : Type u} {B : Type v}
  (h : isCoreduced B) (f : A → B) : Π x, Im.rec h f (Im.unit x) = f x :=
Im.ind.βrule (λ _, h) f

noncomputable hott def Im.app {A : Type u} {B : Type v}
  (f : A → B) : Im A → Im B :=
Im.rec (Im.coreduced B) (Im.unit ∘ f)

noncomputable hott def Im.naturality {A : Type u} {B : Type v}
  (f : A → B) (x : A) : Im.unit (f x) = Im.app f (Im.unit x) :=
begin symmetry; apply Im.rec.βrule end

end GroundZero.HITs.Infinitesimal