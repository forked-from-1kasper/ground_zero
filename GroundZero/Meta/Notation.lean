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

macro "λ " xs:many1(funBinder) ", " f:term : term => `(fun $xs* => $f)
macro xs:many1(funBinder) " ↦ " f:term : term => `(fun $xs* => $f)

macro "begin " ts:sepBy1(tactic, ";", "; ", allowTrailingSep) i:"end" : term =>
  `(by { $[($ts:tactic)]* }%$i)

section
  macro "reflexivity"  : tactic => `(apply Reflexive.intro)
  macro "symmetry"     : tactic => `(apply Symmetric.intro)
  macro "transitivity" : tactic => `(apply Transitive.intro)
end

declare_syntax_cat superscriptNumeral
syntax "⁰" : superscriptNumeral
syntax "¹" : superscriptNumeral
syntax "²" : superscriptNumeral
syntax "³" : superscriptNumeral
syntax "⁴" : superscriptNumeral
syntax "⁵" : superscriptNumeral
syntax "⁶" : superscriptNumeral
syntax "⁷" : superscriptNumeral
syntax "⁸" : superscriptNumeral
syntax "⁹" : superscriptNumeral

def parseNumeral : Lean.Syntax → Nat
| `(superscriptNumeral| ⁰) => 0
| `(superscriptNumeral| ¹) => 1
| `(superscriptNumeral| ²) => 2
| `(superscriptNumeral| ³) => 3
| `(superscriptNumeral| ⁴) => 4
| `(superscriptNumeral| ⁵) => 5
| `(superscriptNumeral| ⁶) => 6
| `(superscriptNumeral| ⁷) => 7
| `(superscriptNumeral| ⁸) => 8
| `(superscriptNumeral| ⁹) => 9
| _                        => 0

def parseNumber (stx : Array Lean.Syntax) :=
let ns := Array.mapIdx stx.reverse (fun i s => parseNumeral s * 10 ^ i.val)
let n  := Array.foldl (· + ·) 0 ns
Lean.Syntax.mkNumLit (toString n)

declare_syntax_cat superscriptChar

syntax "ᵃ" : superscriptChar syntax "ᵇ" : superscriptChar
syntax "ᶜ" : superscriptChar syntax "ᵈ" : superscriptChar
syntax "ᵉ" : superscriptChar syntax "ᶠ" : superscriptChar
syntax "ᵍ" : superscriptChar syntax "ʰ" : superscriptChar
syntax "ⁱ" : superscriptChar syntax "ʲ" : superscriptChar
syntax "ᵏ" : superscriptChar syntax "ˡ" : superscriptChar
syntax "ᵐ" : superscriptChar syntax "ⁿ" : superscriptChar
syntax "ᵒ" : superscriptChar syntax "ᵖ" : superscriptChar
syntax "ʳ" : superscriptChar syntax "ˢ" : superscriptChar
syntax "ᵗ" : superscriptChar syntax "ᵘ" : superscriptChar
syntax "ᵛ" : superscriptChar syntax "ʷ" : superscriptChar
syntax "ˣ" : superscriptChar syntax "ʸ" : superscriptChar

syntax "ᴬ" : superscriptChar syntax "ᴮ" : superscriptChar
syntax "ᴰ" : superscriptChar syntax "ᴱ" : superscriptChar
syntax "ᴳ" : superscriptChar syntax "ᴴ" : superscriptChar
syntax "ᴵ" : superscriptChar syntax "ᴶ" : superscriptChar
syntax "ᴷ" : superscriptChar syntax "ᴸ" : superscriptChar
syntax "ᴹ" : superscriptChar syntax "ᴺ" : superscriptChar
syntax "ᴼ" : superscriptChar syntax "ᴾ" : superscriptChar
syntax "ᴿ" : superscriptChar syntax "ᵀ" : superscriptChar
syntax "ᵁ" : superscriptChar syntax "ⱽ" : superscriptChar
syntax "ᵂ" : superscriptChar

def parseChar : Lean.Syntax → Char
| `(superscriptChar| ᵃ) => 'a' | `(superscriptChar| ᵇ) => 'b'
| `(superscriptChar| ᶜ) => 'c' | `(superscriptChar| ᵈ) => 'd'
| `(superscriptChar| ᵉ) => 'e' | `(superscriptChar| ᶠ) => 'f'
| `(superscriptChar| ᵍ) => 'g' | `(superscriptChar| ʰ) => 'h'
| `(superscriptChar| ⁱ) => 'i' | `(superscriptChar| ʲ) => 'j'
| `(superscriptChar| ᵏ) => 'k' | `(superscriptChar| ˡ) => 'l'
| `(superscriptChar| ᵐ) => 'm' | `(superscriptChar| ⁿ) => 'n'
| `(superscriptChar| ᵒ) => 'o' | `(superscriptChar| ᵖ) => 'p'
| `(superscriptChar| ʳ) => 'r' | `(superscriptChar| ˢ) => 's'
| `(superscriptChar| ᵗ) => 't' | `(superscriptChar| ᵘ) => 'u'
| `(superscriptChar| ᵛ) => 'v' | `(superscriptChar| ʷ) => 'w'
| `(superscriptChar| ˣ) => 'x' | `(superscriptChar| ʸ) => 'y'
| `(superscriptChar| ᴬ) => 'A' | `(superscriptChar| ᴮ) => 'B'
| `(superscriptChar| ᴰ) => 'D' | `(superscriptChar| ᴱ) => 'E'
| `(superscriptChar| ᴳ) => 'G' | `(superscriptChar| ᴴ) => 'H'
| `(superscriptChar| ᴵ) => 'I' | `(superscriptChar| ᴶ) => 'J'
| `(superscriptChar| ᴷ) => 'K' | `(superscriptChar| ᴸ) => 'L'
| `(superscriptChar| ᴹ) => 'M' | `(superscriptChar| ᴺ) => 'N'
| `(superscriptChar| ᴼ) => 'O' | `(superscriptChar| ᴾ) => 'P'
| `(superscriptChar| ᴿ) => 'R' | `(superscriptChar| ᵀ) => 'T'
| `(superscriptChar| ᵁ) => 'U' | `(superscriptChar| ⱽ) => 'V'
| `(superscriptChar| ᵂ) => 'W' | _                     => 'A'

def parseIdent (stx : Array Lean.Syntax) :=
String.mk (Array.map parseChar stx).toList

end GroundZero.Meta.Notation