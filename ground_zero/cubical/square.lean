import ground_zero.cubical.cubes ground_zero.cubical.path
open ground_zero.HITs (I) ground_zero.cubical ground_zero.types

/-
  * Constant square.
  * Connections (∧, ∨) in squares.
-/

namespace ground_zero.cubical.Square
universe u

@[hott] def const {A : Type u} (a : A) :
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

@[hott] def and {A : Type u} {a b : A}
  (p : Path A a b) : Square a a a b :=
lam (λ i j, p # i ∧ j)

@[hott] def or {A : Type u} {a b : A}
  (p : Path A a b) : Square a b b b :=
lam (λ i j, p # i ∨ j)

end ground_zero.cubical.Square