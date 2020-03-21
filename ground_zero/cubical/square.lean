import ground_zero.cubical.path
open ground_zero.HITs (I) ground_zero.cubical ground_zero.types

/-
  * Constant square.
  * Connections (∧, ∨) in squares.
-/

namespace ground_zero.cubical.Square
universe u

@[hott] def lam {α : Type u} (f : I → I → α) :
  Square (f 0) (f 1) (<i> f i 0) (<i> f i 1) :=
Cube.lambda 1 f

@[hott] def const {α : Type u} (a : α) :
  Square (λ _, a) (λ _, a) (<i> a) (<i> a) :=
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
  (p : a ⇝ b) : Square (λ _, a) (λ i, p # i) (<i> a) p :=
lam (λ i j, p # i ∧ j)

@[hott] def or {α : Type u} {a b : α}
  (p : a ⇝ b) : Square (λ i, p # i) (λ _, b) p (<i> b) :=
lam (λ i j, p # i ∨ j)

/-
def Square.compute {α : Type u} {m n : I → α}
  {o : m 0 ⇝ n 0} {p : m 1 ⇝ n 1}
  (s : Square m n o p) : Π i, m i ⇝ n i
-/

end ground_zero.cubical.Square