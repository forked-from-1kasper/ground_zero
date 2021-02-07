import Lean.Parser
open Lean.Parser.Term

namespace GroundZero.Meta.Notation

syntax "Π" many1(simpleBinder <|> bracketedBinder) ", " term : term
macro_rules | `(Π $xs*, $y) => `(∀ $xs*, $y)

notation x "↦" f => fun x => f

macro "begin " ts:tactic,*,? "end"%i : term => do
  `(by { $[$ts:tactic]* }%$i)

end GroundZero.Meta.Notation