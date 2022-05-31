import GroundZero.HITs.Graph
open GroundZero.Types.Equiv (pathoverOfEq)

/-
  Generalized circle or one-step truncation.
  * https://homotopytypetheory.org/2015/07/28/constructing-the-propositional-truncation-using-nonrecursive-hits/
  * https://arxiv.org/pdf/1512.02274
-/

namespace GroundZero.HITs
universe u v

inductive Generalized.rel (α : Type u) : α → α → Type u
| mk : Π (a b : α), rel α a b

def Generalized (α : Type u) := Graph (Generalized.rel α)
notation "{" α "}" => Generalized α

namespace Generalized
  def incl {α : Type u} : α → {α} := Graph.elem

  hott def glue {α : Type u} (a b : α) : incl a = incl b :=
  Graph.line (Generalized.rel.mk a b)

  hott def ind {α : Type u} {π : {α} → Type v} (inclπ : Π a, π (incl a))
    (glueπ : Π a b, inclπ a =[glue a b] inclπ b) : Π x, π x :=
  begin fapply Graph.ind; exact inclπ; { intros u v H; induction H; apply glueπ } end

  attribute [eliminator] ind

  hott def rec {α : Type u} {π : Type v} (inclπ : α → π)
    (glueπ : Π a b, inclπ a = inclπ b) : {α} → π :=
  ind inclπ (λ a b, pathoverOfEq (glue a b) (glueπ a b))

  hott def rep (α : Type u) : ℕ → Type u
  | Nat.zero   => α
  | Nat.succ n => {rep α n}

  example (α : Type u) (n : ℕ) : rep α n → rep α (n + 1) := incl
end Generalized

end GroundZero.HITs