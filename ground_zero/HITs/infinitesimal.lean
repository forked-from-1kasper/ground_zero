import ground_zero.types.equiv
open ground_zero.types.equiv (biinv)

/-
  The modality of shape infinitesimal in cohesive infinity topos.
  https://github.com/groupoid/cubical/blob/master/src/infinitesimal.ctt

  * HoTT 7.7 Modalities
-/

hott theory

namespace ground_zero.HITs.infinitesimal
universes u v

axiom im : Type u → Type u
constant im.unit {α : Type u} : α → im α

def is_coreduced (α : Type u) := biinv (@im.unit α)
axiom im.coreduced (α : Type u) : is_coreduced (im α)

constant im.ind {α : Type u} {β : im α → Type v}
  (h : Π (i : im α), is_coreduced (β i))
  (f : Π (x : α), β (im.unit x)) :
  Π (x : im α), β x

constant im.ind.βrule {α : Type u} {β : im α → Type v}
  (h : Π (i : im α), is_coreduced (β i))
  (f : Π (x : α), β (im.unit x)) :
  Π (x : α), im.ind h f (im.unit x) = f x

@[hott] noncomputable def im.rec {α : Type u} {β : Type v}
  (h : is_coreduced β) (f : α → β) : im α → β :=
im.ind (λ _, h) f

@[hott] noncomputable def im.rec.βrule {α : Type u} {β : Type v}
  (h : is_coreduced β) (f : α → β) :
  Π (x : α), im.rec h f (im.unit x) = f x :=
im.ind.βrule (λ _, h) f

@[hott] noncomputable def im.app {α : Type u} {β : Type v}
  (f : α → β) : im α → im β :=
im.rec (im.coreduced β) (im.unit ∘ f)

@[hott] noncomputable def im.naturality {α : Type u} {β : Type v} (f : α → β) :
  Π (x : α), im.unit (f x) = im.app f (im.unit x) :=
begin intro x, symmetry, transitivity, apply im.rec.βrule, trivial end

end ground_zero.HITs.infinitesimal