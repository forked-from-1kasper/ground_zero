import ground_zero.HITs.graph
open ground_zero.types.equiv

hott theory

/-
  Pushout.
  * HoTT 6.8
-/

namespace ground_zero
namespace HITs

universes u v w k

section
  parameters {α : Type u} {β : Type v} {σ : Type k} (f : σ → α) (g : σ → β)
  inductive pushout_rel : (α ⊕ β) → (α ⊕ β) → Type k
  | mk {} : Π (x : σ), pushout_rel (sum.inl (f x)) (sum.inr (g x))
  def pushout := graph pushout_rel
end

namespace pushout
  -- https://github.com/leanprover/lean2/blob/master/hott/hit/pushout.hlean
  variables {α : Type u} {β : Type v} {σ : Type k} {f : σ → α} {g : σ → β}
  @[hott] def inl (x : α) : pushout f g :=
  graph.elem (sum.inl x)

  @[hott] def inr (x : β) : pushout f g :=
  graph.elem (sum.inr x)

  @[hott] def glue (x : σ) : inl (f x) = inr (g x) :> pushout f g :=
  graph.line (pushout_rel.mk x)

  @[hott] def ind {δ : pushout f g → Type w}
    (inl₁ : Π (x : α), δ (inl x)) (inr₁ : Π (x : β), δ (inr x))
    (glue₁ : Π (x : σ), inl₁ (f x) =[glue x] inr₁ (g x)) :
    Π (x : pushout f g), δ x :=
  begin
    fapply graph.ind,
    { intro x, induction x, apply inl₁, apply inr₁ },
    { intros u v H, induction H with x, apply glue₁ }
  end

  @[hott] def rec {δ : Type w} (inl₁ : α → δ) (inr₁ : β → δ)
    (glue₁ : Π (x : σ), inl₁ (f x) = inr₁ (g x)) :
    pushout f g → δ :=
  ind inl₁ inr₁ (λ x, pathover_of_eq (glue x) (glue₁ x))

  @[hott] noncomputable def indβrule {δ : pushout f g → Type w}
    (inl₁ : Π (x : α), δ (inl x)) (inr₁ : Π (x : β), δ (inr x))
    (glue₁ : Π (x : σ), inl₁ (f x) =[glue x] inr₁ (g x)) (x : σ) :
    apd (ind inl₁ inr₁ glue₁) (glue x) = glue₁ x :=
  by apply graph.indβrule

  @[hott] noncomputable def recβrule {δ : Type w} (inl₁ : α → δ) (inr₁ : β → δ)
    (glue₁ : Π x, inl₁ (f x) = inr₁ (g x)) (x : σ) :
    (rec inl₁ inr₁ glue₁) # (glue x) = glue₁ x :=
  begin
    apply types.equiv.pathover_of_eq_inj (glue x), transitivity,
    symmetry, apply types.equiv.apd_over_constant_family,
    transitivity, apply indβrule, reflexivity
  end
end pushout

end HITs
end ground_zero