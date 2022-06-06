import GroundZero.HITs.Graph
open GroundZero.Types.Equiv
open GroundZero.Types

/-
  Pushout.
  * HoTT 6.8
-/

namespace GroundZero
namespace HITs

universe u v w k

section
  variable {α : Type u} {β : Type v} {σ : Type k} (f : σ → α) (g : σ → β)

  inductive Pushout.rel : (α ⊕ β) → (α ⊕ β) → Type k
  | mk : Π (x : σ), rel (Sum.inl (f x)) (Sum.inr (g x))

  def Pushout := Graph (Pushout.rel f g)
end

namespace Pushout
  -- https://github.com/leanprover/lean2/blob/master/hott/hit/Pushout.hlean
  variable {α : Type u} {β : Type v} {σ : Type k} {f : σ → α} {g : σ → β}

  hott def inl (x : α) : Pushout f g :=
  Graph.elem (Sum.inl x)

  hott def inr (x : β) : Pushout f g :=
  Graph.elem (Sum.inr x)

  hott def glue (x : σ) : @inl _ _ _ f g (f x) = inr (g x) :=
  Graph.line (Pushout.rel.mk x)

  hott def ind {π : Pushout f g → Type w} (inlπ : Π x, π (inl x)) (inrπ : Π x, π (inr x))
    (glueπ : Π x, inlπ (f x) =[glue x] inrπ (g x)) : Π x, π x :=
  begin
    fapply Graph.ind; { intro x; induction x using Sum.casesOn; apply inlπ; apply inrπ };
    { intros u v H; induction H; apply glueπ }
  end

  attribute [eliminator] ind

  hott def rec {π : Type w} (inlπ : α → π) (inrπ : β → π)
    (glueπ : Π x, inlπ (f x) = inrπ (g x)) : Pushout f g → π :=
  ind inlπ inrπ (λ x, pathoverOfEq (glue x) (glueπ x))

  noncomputable hott def indβrule {π : Pushout f g → Type w}
    (inlπ : Π x, π (inl x)) (inrπ : Π x, π (inr x))
    (glueπ : Π x, inlπ (f x) =[glue x] inrπ (g x)) (x : σ) :
    apd (ind inlπ inrπ glueπ) (glue x) = glueπ x :=
  @Graph.indβrule _ (rel f g) _ _ _ _ _ (rel.mk x)

  noncomputable hott def recβrule {π : Type w} (inlπ : α → π) (inrπ : β → π)
    (glueπ : Π x, inlπ (f x) = inrπ (g x)) (x : σ) :
    Id.map (rec inlπ inrπ glueπ) (glue x) = glueπ x :=
  begin
    apply pathoverOfEqInj (glue x); transitivity;
    symmetry; apply apdOverConstantFamily;
    transitivity; apply indβrule; reflexivity
  end
end Pushout

end HITs
end GroundZero