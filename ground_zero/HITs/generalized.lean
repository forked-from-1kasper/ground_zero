import ground_zero.HITs.graph
open ground_zero.types.dep_path (pathover_of_eq)

/-
  Generalized circle or one-step truncation.
  * https://homotopytypetheory.org/2015/07/28/constructing-the-propositional-truncation-using-nonrecursive-hits/
  * https://arxiv.org/pdf/1512.02274
-/

namespace ground_zero.HITs
universes u v

inductive generalized.rel (α : Sort u) : α → α → Sort u
| mk {} : Π (a b : α), generalized.rel a b

def generalized (α : Sort u) := graph (generalized.rel α)
notation `{` α `}` := generalized α

namespace generalized
  def incl {α : Sort u} : α → {α} := graph.elem

  def glue {α : Sort u} (a b : α) :
    incl a = incl b :> {α} :=
  graph.line (generalized.rel.mk a b)

  def ind
    {α : Sort u} {π : {α} → Sort v}
    (incl₁ : Π (a : α), π (incl a))
    (glue₁ : Π (a b : α), incl₁ a =[glue a b] incl₁ b) :
    Π (x : generalized α), π x := begin
    fapply graph.ind, exact incl₁,
    { intros u v H, cases H, apply glue₁ }
  end

  def rec {α : Sort u} {π : Sort v}
    (incl₁ : α → π) (glue₁ : Π (a b : α), incl₁ a = incl₁ b :> π) :
    {α} → π :=
  ind incl₁ (λ a b, pathover_of_eq (glue a b) (glue₁ a b))

  def repeat (α : Sort u) : ℕ → Sort u
  | 0 := α
  | (n + 1) := {repeat n}

  def dep (α : Sort u) (n : ℕ) : repeat α n → repeat α (n + 1) :=
  incl
end generalized

end ground_zero.HITs