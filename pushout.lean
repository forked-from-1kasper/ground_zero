namespace ground_zero
universe u

section
  parameters {α β σ : Type u} (f : σ → α) (g : σ → β)
  inductive pushout_rel : (α ⊕ β) → (α ⊕ β) → Prop
  | mk {} : Π (x : σ), pushout_rel (sum.inl (f x)) (sum.inr (g x))
  def pushout := quot pushout_rel
end

namespace pushout
  -- https://github.com/leanprover/lean2/blob/master/hott/hit/pushout.hlean
  variables {α β σ : Type u} {f : σ → α} {g : σ → β}
  def inl (x : α) : pushout f g :=
  quot.mk (pushout_rel f g) (sum.inl x)

  def inr (x : β) : pushout f g :=
  quot.mk (pushout_rel f g) (sum.inr x)

  def glue (x : σ) : inl (f x) = inr (g x) :=
  quot.sound (pushout_rel.mk x)
end pushout

end ground_zero