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
  variable {A : Type u} {B : Type v} {C : Type k} (f : C → A) (g : C → B)

  inductive Pushout.rel : (A ⊕ B) → (A ⊕ B) → Type k
  | mk : Π (x : C), rel (Sum.inl (f x)) (Sum.inr (g x))

  def Pushout := Graph (Pushout.rel f g)
end

namespace Pushout
  -- https://github.com/leanprover/lean2/blob/master/hott/hit/Pushout.hlean
  variable {A : Type u} {B : Type v} {C : Type k} {f : C → A} {g : C → B}

  hott def inl (x : A) : Pushout f g :=
  Graph.elem (Sum.inl x)

  hott def inr (x : B) : Pushout f g :=
  Graph.elem (Sum.inr x)

  hott def glue (x : C) : @inl _ _ _ f g (f x) = inr (g x) :=
  Graph.line (Pushout.rel.mk x)

  hott def ind {P : Pushout f g → Type w} (inlπ : Π x, P (inl x)) (inrπ : Π x, P (inr x))
    (glueπ : Π x, inlπ (f x) =[glue x] inrπ (g x)) : Π x, P x :=
  begin
    fapply Graph.ind; { intro x; induction x using Sum.casesOn; apply inlπ; apply inrπ };
    { intros u v H; induction H; apply glueπ }
  end

  attribute [eliminator] ind

  hott def rec {D : Type w} (inlπ : A → D) (inrπ : B → D)
    (glueπ : Π x, inlπ (f x) = inrπ (g x)) : Pushout f g → D :=
  ind inlπ inrπ (λ x, pathoverOfEq (glue x) (glueπ x))

  noncomputable hott def indβrule {P : Pushout f g → Type w}
    (inlπ : Π x, P (inl x)) (inrπ : Π x, P (inr x))
    (glueπ : Π x, inlπ (f x) =[glue x] inrπ (g x)) (x : C) :
    apd (ind inlπ inrπ glueπ) (glue x) = glueπ x :=
  @Graph.indβrule _ (rel f g) _ _ _ _ _ (rel.mk x)

  noncomputable hott def recβrule {D : Type w} (inlπ : A → D) (inrπ : B → D)
    (glueπ : Π x, inlπ (f x) = inrπ (g x)) (x : C) :
    Id.map (rec inlπ inrπ glueπ) (glue x) = glueπ x :=
  begin
    apply pathoverOfEqInj (glue x); transitivity;
    symmetry; apply apdOverConstantFamily;
    transitivity; apply indβrule; reflexivity
  end
end Pushout

end HITs
end GroundZero