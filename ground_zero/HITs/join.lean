import ground_zero.HITs.pushout
open ground_zero.types.product (pr₁ pr₂)

namespace ground_zero.HITs
local infix ` = ` := ground_zero.types.eq

universes u v
def join (α : Type u) (β : Type v) :=
@pushout α β (α × β) pr₁ pr₂

namespace join
  variables {α : Type u} {β : Type v}

  def inl : α → join α β := pushout.inl
  def inr : β → join α β := pushout.inr

  def push (a : α) (b : β) : inl a = inr b :=
  pushout.glue (ground_zero.types.product.intro a b)
end join

end ground_zero.HITs