import ground_zero.HITs.pushout
open ground_zero.types.product (pr₁ pr₂)

hott theory

namespace ground_zero.HITs

universes u v w
def join (α : Type u) (β : Type v) :=
@pushout α β (α × β) pr₁ pr₂

namespace join
  variables {α : Type u} {β : Type v}

  def inl : α → join α β := pushout.inl
  def inr : β → join α β := pushout.inr

  def push (a : α) (b : β) : inl a = inr b :=
  pushout.glue (ground_zero.types.product.intro a b)

  def ind {π : join α β → Type w}
    (inl₁ : Π (x : α), π (inl x))
    (inr₁ : Π (x : β), π (inr x))
    (push₁ : Π (a : α) (b : β), inl₁ a =[push a b] inr₁ b) :
    Π (x : join α β), π x :=
  pushout.ind inl₁ inr₁
    (begin intro x, cases x with u v, exact push₁ u v end)
end join

end ground_zero.HITs