import Lean.Parser
open Lean.Parser.Term

section
  variable {α : Type u} (ρ : α → α → Type v)

  class Reflexive :=
  (intro : ρ a a)

  class Symmetric :=
  (intro : ρ a b → ρ b a)

  class Transitive :=
  (intro : ρ a b → ρ b c → ρ a c)
end

namespace GroundZero.Meta.Notation

syntax "Π" many1(simpleBinder <|> bracketedBinder) ", " term : term
macro_rules | `(Π $xs*, $y) => `(∀ $xs*, $y)

notation x "↦" f => fun x => f

macro "begin " ts:tactic,*,? i:"end" : term => do
  `(by { $[$ts:tactic]* }%$i)

section
  macro "reflexivity" : tactic => `(apply Reflexive.intro)
  macro "symmetry"    : tactic => `(apply Symmetric.intro)
  macro "transtivity" : tactic => `(apply Transitive.intro)
end

end GroundZero.Meta.Notation