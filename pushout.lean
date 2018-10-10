namespace ground_zero
universes u v k j

section
  parameters {α : Type u} {β : Type v} {σ : Type k} (f : σ → α) (g : σ → β)
  inductive pushout_rel : (α ⊕ β) → (α ⊕ β) → Prop
  | mk {} : Π (x : σ), pushout_rel (sum.inl (f x)) (sum.inr (g x))
  def pushout := quot pushout_rel
end

namespace pushout
  -- https://github.com/leanprover/lean2/blob/master/hott/hit/pushout.hlean
  variables {α : Type u} {β : Type v} {σ : Type k} {f : σ → α} {g : σ → β}
  def inl (x : α) : pushout f g :=
  quot.mk (pushout_rel f g) (sum.inl x)

  def inr (x : β) : pushout f g :=
  quot.mk (pushout_rel f g) (sum.inr x)

  def glue (x : σ) : inl (f x) = inr (g x) :=
  quot.sound (pushout_rel.mk x)

  def rec {δ : Type j} (inl₁ : α → δ) (inr₁ : β → δ)
    (glue₁ : Π (x : σ), inl₁ (f x) = inr₁ (g x)) : pushout f g → δ := begin
    intro h, apply @quot.lift (α ⊕ β) (pushout_rel f g) δ
    (begin intro x, cases x, apply inl₁ x, apply inr₁ x end),
    intros a b H, cases H with x, simp, apply glue₁ x,
    assumption
  end
end pushout

end ground_zero