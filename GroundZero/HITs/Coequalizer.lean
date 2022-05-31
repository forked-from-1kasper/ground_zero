import GroundZero.HITs.Graph
open GroundZero.Types.Equiv
open GroundZero.Types

namespace GroundZero.HITs
universe u v w

section
  variable {α : Type u} {β : Type v} (f g : α → β)

  inductive Coeq.rel : β → β → Type (max u v)
  | intro : Π x, rel (f x) (g x)

  def Coeq := Graph (Coeq.rel f g)
end

namespace Coeq
  variable {α : Type u} {β : Type v} {f g : α → β}

  hott def iota : β → Coeq f g := Graph.elem
  hott def resp : Π x, @Id (Coeq f g) (iota (f x)) (iota (g x)) :=
  λ x, Graph.line (Coeq.rel.intro x)

  hott def ind (π : Coeq f g → Type w) (i : Π x, π (iota x))
    (ρ : Π x, i (f x) =[resp x] i (g x)) : Π x, π x :=
  begin fapply Graph.ind; apply i; intros x y H; induction H; apply ρ end

  attribute [eliminator] ind

  noncomputable hott def indβrule (π : Coeq f g → Type w) (i : Π x, π (iota x))
    (ρ : Π x, i (f x) =[resp x] i (g x)) (x : α) : apd (ind π i ρ) (resp x) = ρ x :=
  @Graph.indβrule _ (rel f g) _ _ _ _ _ (rel.intro x)

  hott def rec (π : Type w) (i : β → π) (ρ : Π x, i (f x) = i (g x)) : Coeq f g → π :=
  ind (λ _, π) i (λ x, pathoverOfEq (resp x) (ρ x))

  noncomputable hott def recβrule (π : Type w) (i : β → π)
    (ρ : Π x, i (f x) = i (g x)) : Π x, Id.map (rec π i ρ) (resp x) = ρ x :=
  begin
    intro x; apply pathoverOfEqInj (resp x);
    transitivity; symmetry; apply apdOverConstantFamily;
    transitivity; apply indβrule; reflexivity
  end
end Coeq

end GroundZero.HITs