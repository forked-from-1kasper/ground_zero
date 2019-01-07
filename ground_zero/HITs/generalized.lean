import ground_zero.types.heq

namespace ground_zero.HITs
universes u v

inductive generalized.rel {α : Sort u} : α → α → Prop
| mk : Π (a b : α), generalized.rel a b

def generalized (α : Sort u) := @quot α generalized.rel
notation `{` α `}` := generalized α

namespace generalized
  def incl {α : Sort u} (a : α) : {α} :=
  quot.mk rel a

  def glue {α : Sort u} (a b : α) :
    incl a = incl b :> {α} :=
  ground_zero.support.inclusion $ quot.sound
    (generalized.rel.mk a b)

  def ind
    {α : Sort u} {π : {α} → Sort v}
    (incl₁ : Π (a : α), π (incl a))
    (glue₁ : Π (a b : α), incl₁ a =[glue a b] incl₁ b) :
    Π (x : generalized α), π x := begin
    intro x, fapply quot.hrec_on x, clear x,
    { exact incl₁ },
    { intros, clear p,
      fapply ground_zero.types.heq.from_pathover,
      apply glue, apply glue₁ }
  end

  def repeat (α : Sort u) : ℕ → Sort u
  | 0 := α
  | (n + 1) := {repeat n}

  def dep (α : Sort u) (n : ℕ) : repeat α n → repeat α (n + 1) :=
  incl
end generalized

end ground_zero.HITs