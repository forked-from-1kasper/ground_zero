import GroundZero.HITs.Graph
open GroundZero.Types.Equiv (pathoverOfEq)

/-
  Generalized circle or one-step truncation.
  * https://homotopytypetheory.org/2015/07/28/constructing-the-propositional-truncation-using-nonrecursive-hits/
  * https://arxiv.org/pdf/1512.02274
-/

namespace GroundZero.HITs
universe u v

inductive Generalized.rel (A : Type u) : A → A → Type u
| mk : Π (a b : A), rel A a b

def Generalized (A : Type u) := Graph (Generalized.rel A)
notation "{" A "}" => Generalized A

namespace Generalized
  def incl {A : Type u} : A → {A} := Graph.elem

  hott def glue {A : Type u} (a b : A) : incl a = incl b :=
  Graph.line (Generalized.rel.mk a b)

  hott def ind {A : Type u} {B : {A} → Type v} (inclπ : Π a, B (incl a))
    (glueπ : Π a b, inclπ a =[glue a b] inclπ b) : Π x, B x :=
  begin fapply Graph.ind; exact inclπ; { intros u v H; induction H; apply glueπ } end

  attribute [eliminator] ind

  hott def rec {A : Type u} {B : Type v} (inclπ : A → B)
    (glueπ : Π a b, inclπ a = inclπ b) : {A} → B :=
  ind inclπ (λ a b, pathoverOfEq (glue a b) (glueπ a b))

  hott def rep (A : Type u) : ℕ → Type u
  | Nat.zero   => A
  | Nat.succ n => {rep A n}

  hott def dep (A : Type u) (n : ℕ) : rep A n → rep A (n + 1) := incl
end Generalized

end GroundZero.HITs