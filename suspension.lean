import ground_zero.pushout ground_zero.unit

namespace ground_zero

def {u} suspension (α : Type u) :=
pushout (λ (a : α), ground_zero.unit.star) (λ _, ground_zero.unit.star)
notation `∑` := suspension

namespace suspension
  -- https://github.com/leanprover/lean2/blob/master/hott/homotopy/susp.hlean
  universe u

  def north {α : Type u} : suspension α := pushout.inl ground_zero.unit.star
  def south {α : Type u} : suspension α := pushout.inr ground_zero.unit.star

  def merid {α : Type u} (a : α) : north = south :=
  pushout.glue a
end suspension

end ground_zero