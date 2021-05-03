import ground_zero.HITs.merely
open ground_zero.types

hott theory

namespace ground_zero.theorems.logic
  universe u

  inductive wff
  | impl  : wff → wff → wff
  | box   : wff → wff
  | false : wff

  infixr ` ⇒ `:30 := wff.impl
  prefix `□`:90 := wff.box

  notation `⊥` := wff.false

  def not (φ : wff) := φ ⇒ ⊥
  prefix `¬` := not

  def diam (φ : wff) := ¬□¬φ
  prefix `◇`:90 := diam

  namespace S5
    inductive deriv : wff → Type
    | mp  : Π φ ψ, deriv (φ ⇒ ψ) → deriv φ → deriv ψ
    | nec : Π φ, deriv φ → deriv □φ
    | ak  : Π φ ψ, deriv (φ ⇒ ψ ⇒ φ)
    | as  : Π φ ψ ξ, deriv ((φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ))
    | ac  : Π φ ψ, deriv ((¬φ ⇒ ¬ψ) ⇒ (ψ ⇒ φ))
    | K   : Π φ ψ, deriv (□(φ ⇒ ψ) ⇒ □φ ⇒ □ψ)
    | T   : Π φ, deriv (□φ ⇒ φ)
    | «5» : Π φ, deriv (◇φ ⇒ □◇φ)
  end S5

  prefix `⊢₅ `:25 := S5.deriv

  def I (φ : wff) : ⊢₅ φ ⇒ φ := begin
    apply S5.deriv.mp,
    { apply S5.deriv.mp,
      apply S5.deriv.as φ (φ ⇒ φ) φ,
      apply S5.deriv.ak },
    apply S5.deriv.ak
  end
end ground_zero.theorems.logic