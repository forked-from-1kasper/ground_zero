import ground_zero.cubical.path
open ground_zero.HITs (I) ground_zero.cubical ground_zero.types

/-
  * Constant square.
  * Connections (∧, ∨) in squares.
-/

namespace ground_zero.cubical.Square
universe u

@[hott] def const {α : Type u} (a : α) :
  Square a a a a :=
lam (λ i j, a)

/-
                     p
          a -----------------> b
          ^                    ^
          |                    |
          |                    |
    <j> a |        and p       | p
          |                    |
          |                    |
          |                    |
          a -----------------> a
                   <i> a
-/
@[hott] def and {α : Type u} {a b : α}
  (p : a ⇝ b) : Square a a a b :=
lam (λ i j, p # i ∧ j)

@[hott] def or {α : Type u} {a b : α}
  (p : a ⇝ b) : Square a b b b :=
lam (λ i j, p # i ∨ j)

end ground_zero.cubical.Square