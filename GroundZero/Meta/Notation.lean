import Lean.Parser import Lean.Elab.Command
open Lean.Parser Lean.Parser.Term Lean.Elab.Command

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

macro "begin " ts:sepBy1(tactic, ";", "; ", allowTrailingSep) i:"end" : term =>
  `(by { $[($ts:tactic)]* }%$i)

section
  macro "reflexivity" : tactic => `(apply Reflexive.intro)
  macro "symmetry"    : tactic => `(apply Symmetric.intro)
  macro "transtivity" : tactic => `(apply Transitive.intro)
end

end GroundZero.Meta.Notation