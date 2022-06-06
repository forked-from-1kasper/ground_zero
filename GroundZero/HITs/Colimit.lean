import GroundZero.HITs.Graph
open GroundZero.Types.Equiv (pathoverOfEq)

/-
  Sequential Colimit.
  * https://homotopytypetheory.org/2016/01/08/Colimits-in-hott/
-/

namespace GroundZero.HITs
universe u v

inductive Colimit.core (α : ℕ → Type u)
  (f : Π (n : ℕ), α n → α (n + 1))
| incl {n : ℕ} : α n → core α f

inductive Colimit.rel (α : ℕ → Type u) (f : Π (n : ℕ), α n → α (n + 1)) :
  Colimit.core α f → Colimit.core α f → Type u
| glue (n : ℕ) (x : α n) : rel α f (core.incl (f n x)) (core.incl x)

hott def Colimit (α : ℕ → Type u) (f : Π (n : ℕ), α n → α (n + 1)) :=
Graph (Colimit.rel α f)

namespace Colimit
  variable {α : ℕ → Type u} {f : Π (n : ℕ), α n → α (n + 1)}

  hott def incl {n : ℕ} (x : α n) : Colimit α f :=
  Graph.elem (core.incl x)

  hott def inclusion (n : ℕ) : α n → Colimit α f := incl

  hott def glue {n : ℕ} (x : α n) : incl (f n x) = @incl α f n x :=
  Graph.line (Colimit.rel.glue n x)

  hott def ind {π : Colimit α f → Type v} (inclπ : Π (n : ℕ) (x : α n), π (incl x))
    (glueπ : Π (n : ℕ) (x : α n), inclπ (n + 1) (f n x) =[glue x] inclπ n x) : Π x, π x :=
  begin
    intro x; fapply Graph.ind;
    { intro (core.incl x); apply inclπ };
    { intros u v H; induction H; apply glueπ }
  end

  attribute [eliminator] ind

  hott def rec {π : Type v} (inclπ : Π (n : ℕ) (x : α n), π)
    (glueπ : Π (n : ℕ) (x : α n), inclπ (n + 1) (f n x) = inclπ n x) : Colimit α f → π :=
  ind @inclπ (λ n x, pathoverOfEq (glue x) (glueπ n x))
end Colimit

end GroundZero.HITs