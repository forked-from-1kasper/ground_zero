import Lean.Parser import Lean.Elab.Command
open Lean.Parser Lean.Parser.Term Lean.Elab.Command

namespace GroundZero.Meta.Notation

syntax "Π" many1(binderIdent <|> bracketedBinder) ", " term : term
macro_rules | `(Π $xs*, $y) => `(∀ $xs*, $y)

macro "λ " xs:many1(funBinder) ", " f:term : term => `(fun $xs* => $f)
macro xs:many1(funBinder) " ↦ " f:term : term => `(fun $xs* => $f)

macro "begin " ts:sepBy1(tactic, ";", "; ", allowTrailingSep) i:"end" : term =>
  `(by { $[($ts:tactic)]* }%$i)

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

def parseSupNumeral : Lean.Syntax → Nat
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

declare_syntax_cat subscriptNumeral
syntax "₀" : subscriptNumeral
syntax "₁" : subscriptNumeral
syntax "₂" : subscriptNumeral
syntax "₃" : subscriptNumeral
syntax "₄" : subscriptNumeral
syntax "₅" : subscriptNumeral
syntax "₆" : subscriptNumeral
syntax "₇" : subscriptNumeral
syntax "₈" : subscriptNumeral
syntax "₉" : subscriptNumeral

def parseSubNumeral : Lean.Syntax → Nat
| `(subscriptNumeral| ₀) => 0
| `(subscriptNumeral| ₁) => 1
| `(subscriptNumeral| ₂) => 2
| `(subscriptNumeral| ₃) => 3
| `(subscriptNumeral| ₄) => 4
| `(subscriptNumeral| ₅) => 5
| `(subscriptNumeral| ₆) => 6
| `(subscriptNumeral| ₇) => 7
| `(subscriptNumeral| ₈) => 8
| `(subscriptNumeral| ₉) => 9
| _                      => 0

def parseNumber (φ : Lean.Syntax → Nat) (stx : Array Lean.Syntax) :=
let ns := Array.mapIdx stx.reverse (fun i s => φ s * 10 ^ i.val)
let n  := Array.foldl (· + ·) 0 ns
Lean.Syntax.mkNumLit (toString n)

def parseSupNumber := parseNumber parseSupNumeral
def parseSubNumber := parseNumber parseSubNumeral

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

def parseSupChar : Lean.Syntax → Char
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

declare_syntax_cat subscriptChar

syntax "ₐ" : subscriptChar syntax "ₑ" : subscriptChar
syntax "ₕ" : subscriptChar syntax "ᵢ" : subscriptChar
syntax "ⱼ" : subscriptChar syntax "ₖ" : subscriptChar
syntax "ₗ" : subscriptChar syntax "ₘ" : subscriptChar
syntax "ₙ" : subscriptChar syntax "ₒ" : subscriptChar
syntax "ₚ" : subscriptChar syntax "ᵣ" : subscriptChar
syntax "ₛ" : subscriptChar syntax "ₜ" : subscriptChar
syntax "ᵤ" : subscriptChar syntax "ᵥ" : subscriptChar
syntax "ₓ" : subscriptChar

def parseSubChar : Lean.Syntax → Char
| `(subscriptChar| ₐ) => 'a' | `(subscriptChar| ₑ) => 'e'
| `(subscriptChar| ₕ) => 'h' | `(subscriptChar| ᵢ) => 'i'
| `(subscriptChar| ⱼ) => 'j' | `(subscriptChar| ₖ) => 'k'
| `(subscriptChar| ₗ) => 'l' | `(subscriptChar| ₘ) => 'm'
| `(subscriptChar| ₙ) => 'n' | `(subscriptChar| ₒ) => 'o'
| `(subscriptChar| ₚ) => 'p' | `(subscriptChar| ᵣ) => 'r'
| `(subscriptChar| ₛ) => 's' | `(subscriptChar| ₜ) => 't'
| `(subscriptChar| ᵤ) => 'u' | `(subscriptChar| ᵥ) => 'v'
| `(subscriptChar| ₓ) => 'x' | _                   => 'a'

def parseIdent (φ : Lean.Syntax → Char) (stx : Array Lean.Syntax) :=
String.mk (Array.map φ stx).toList

def parseSubIdent := parseIdent parseSubChar
def parseSupIdent := parseIdent parseSupChar

declare_syntax_cat superscript
syntax (name := superscriptNumber) many1(superscriptNumeral) : superscript
syntax (name := superscriptIdent)  many1(superscriptChar)    : superscript

def parseSuperscript : Lean.Syntax → Lean.MacroM Lean.Term
| `(superscriptNumber| $stx*) => return parseSupNumber stx
| `(superscriptIdent| $stx*) => return Lean.mkIdent (parseSupIdent stx)
| stx => Lean.Macro.throwError "invalid superscript"

declare_syntax_cat subscript
syntax (name := subscriptNumber) many1(subscriptNumeral) : subscript
syntax (name := subscriptIdent)  many1(subscriptChar)    : subscript

def parseSubscript : Lean.Syntax → Lean.MacroM Lean.Term
| `(subscriptNumber| $stx*) => return parseSubNumber stx
| `(subscriptIdent| $stx*) => return Lean.mkIdent (parseSubIdent stx)
| stx => Lean.Macro.throwError "invalid subscript"

end GroundZero.Meta.Notation