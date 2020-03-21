import ground_zero.HITs.graph
open ground_zero.types.equiv (pathover_of_eq)

/-
  Generalized circle or one-step truncation.
  * https://homotopytypetheory.org/2015/07/28/constructing-the-propositional-truncation-using-nonrecursive-hits/
  * https://arxiv.org/pdf/1512.02274
-/

namespace ground_zero.HITs
universes u v

inductive generalized.rel (α : Type u) : α → α → Type u
| mk {} : Π (a b : α), generalized.rel a b

def generalized (α : Type u) := graph (generalized.rel α)
notation `{` α `}` := generalized α

namespace generalized
  def incl {α : Type u} : α → {α} := graph.elem

  @[hott] def glue {α : Type u} (a b : α) :
    incl a = incl b :> {α} :=
  graph.line (generalized.rel.mk a b)

  @[hott] def ind {α : Type u} {π : {α} → Type v}
    (incl₁ : Π (a : α), π (incl a))
    (glue₁ : Π (a b : α), incl₁ a =[glue a b] incl₁ b) :
    Π (x : generalized α), π x := begin
    fapply graph.ind, exact incl₁,
    { intros u v H, induction H, apply glue₁ }
  end

  @[hott] def rec {α : Type u} {π : Type v}
    (incl₁ : α → π) (glue₁ : Π (a b : α), incl₁ a = incl₁ b :> π) :
    {α} → π :=
  ind incl₁ (λ a b, pathover_of_eq (glue a b) (glue₁ a b))

  @[hott] def repeat (α : Type u) : ℕ → Type u
  | 0 := α
  | (n + 1) := {repeat n}

  @[hott] def dep (α : Type u) (n : ℕ) : repeat α n → repeat α (n + 1) := incl
end generalized

end ground_zero.HITs