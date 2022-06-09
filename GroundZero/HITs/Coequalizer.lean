import GroundZero.HITs.Graph
open GroundZero.Types.Equiv
open GroundZero.Types

namespace GroundZero.HITs
universe u v w

section
  variable {A : Type u} {B : Type v} (f g : A → B)

  inductive Coeq.rel : B → B → Type (max u v)
  | intro : Π x, rel (f x) (g x)

  def Coeq := Graph (Coeq.rel f g)
end

namespace Coeq
  variable {A : Type u} {B : Type v} {f g : A → B}

  hott def iota : B → Coeq f g := Graph.elem
  hott def resp : Π x, @Id (Coeq f g) (iota (f x)) (iota (g x)) :=
  λ x, Graph.line (Coeq.rel.intro x)

  hott def ind (C : Coeq f g → Type w) (i : Π x, C (iota x))
    (ρ : Π x, i (f x) =[resp x] i (g x)) : Π x, C x :=
  begin fapply Graph.ind; apply i; intros x y H; induction H; apply ρ end

  attribute [eliminator] ind

  noncomputable hott def indβrule (C : Coeq f g → Type w) (i : Π x, C (iota x))
    (ρ : Π x, i (f x) =[resp x] i (g x)) (x : A) : apd (ind C i ρ) (resp x) = ρ x :=
  @Graph.indβrule _ (rel f g) _ _ _ _ _ (rel.intro x)

  hott def rec (C : Type w) (i : B → C) (ρ : Π x, i (f x) = i (g x)) : Coeq f g → C :=
  ind (λ _, C) i (λ x, pathoverOfEq (resp x) (ρ x))

  noncomputable hott def recβrule (C : Type w) (i : B → C)
    (ρ : Π x, i (f x) = i (g x)) : Π x, Id.map (rec C i ρ) (resp x) = ρ x :=
  begin
    intro x; apply pathoverOfEqInj (resp x);
    transitivity; symmetry; apply apdOverConstantFamily;
    transitivity; apply indβrule; reflexivity
  end
end Coeq

end GroundZero.HITs