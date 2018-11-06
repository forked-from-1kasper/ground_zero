import ground_zero.heq ground_zero.eq ground_zero.support

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

  def glue (x : σ) : inl (f x) = inr (g x) :> pushout f g :=
  support.inclusion $ quot.sound (pushout_rel.mk x)

  def ind {δ : pushout f g → Type j}
    (inl₁ : Π (x : α), δ (inl x)) (inr₁ : Π (x : β), δ (inr x))
    (glue₁ : Π (x : σ), inl₁ (f x) == inr₁ (g x)) : Π (x : pushout f g), δ x := begin
    intro h, apply quot.hrec_on h (begin intro x, cases x, apply inl₁, apply inr₁ end),
    intros a b H, cases H with x, simp, apply glue₁ x
  end

  def rec {δ : Type j} (inl₁ : α → δ) (inr₁ : β → δ)
    (glue₁ : Π (x : σ), inl₁ (f x) = inr₁ (g x) :> δ) :
    pushout f g → δ :=
  @ind α β σ f g (λ _, δ) inl₁ inr₁
    (λ x, heq.inclusion (glue₁ x))
end pushout

end ground_zero