import ground_zero.HITs.pushout ground_zero.types.unit

/-
  Suspension.
  * HoTT 6.5
-/

namespace ground_zero
namespace HITs

abbreviation unit₀ : Type := types.unit
abbreviation star₀ : unit₀ := types.unit.star

def {u} suspension (α : Type u) :=
pushout (λ (a : α), star₀) (λ _, star₀)
notation `∑` := suspension

namespace suspension
  -- https://github.com/leanprover/lean2/blob/master/hott/homotopy/susp.hlean
  universes u v

  def north {α : Type u} : suspension α := pushout.inl types.unit.star
  def south {α : Type u} : suspension α := pushout.inr types.unit.star

  def merid {α : Type u} (a : α) :
    north = south :> suspension α :=
  pushout.glue a

  def ind {α : Type u} {β : ∑α → Type v}
    (n : β north) (s : β south)
    (m : Π (x : α), n =[merid x] s) : Π (x : ∑α), β x :=
  pushout.ind
    (begin intro x, induction x, apply n end)
    (begin intro x, induction x, apply s end)
    (by assumption)

  def rec {α : Type u} {β : Type v} (n s : β)
    (m : α → n = s :> β) : ∑α → β :=
  pushout.rec (λ _, n) (λ _, s) m
end suspension

end HITs
end ground_zero