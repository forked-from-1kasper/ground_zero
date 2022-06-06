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
axiom Im.unit {α : Type u} : α → Im α

def isCoreduced (α : Type u) := biinv (@Im.unit α)
axiom Im.coreduced (α : Type u) : isCoreduced (Im α)

axiom Im.ind {α : Type u} {β : Im α → Type v}
  (h : Π i, isCoreduced (β i)) (f : Π x, β (Im.unit x)) : Π x, β x

axiom Im.ind.βrule {α : Type u} {β : Im α → Type v}
  (h : Π i, isCoreduced (β i)) (f : Π x, β (Im.unit x)) :
  Π x, Im.ind h f (Im.unit x) = f x

noncomputable hott def Im.rec {α : Type u} {β : Type v}
  (h : isCoreduced β) (f : α → β) : Im α → β :=
Im.ind (λ _, h) f

noncomputable hott def Im.rec.βrule {α : Type u} {β : Type v}
  (h : isCoreduced β) (f : α → β) : Π x, Im.rec h f (Im.unit x) = f x :=
Im.ind.βrule (λ _, h) f

noncomputable hott def Im.app {α : Type u} {β : Type v}
  (f : α → β) : Im α → Im β :=
Im.rec (Im.coreduced β) (Im.unit ∘ f)

noncomputable hott def Im.naturality {α : Type u} {β : Type v}
  (f : α → β) (x : α) : Im.unit (f x) = Im.app f (Im.unit x) :=
begin symmetry; apply Im.rec.βrule end

end GroundZero.HITs.Infinitesimal