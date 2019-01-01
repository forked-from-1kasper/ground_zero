import ground_zero.cubical.Path
open ground_zero.HITs (I) ground_zero.cubical
open ground_zero.types

namespace ground_zero.cubical.Square
universe u

def lam {α : Sort u} (f : I → I → α) :
  Square (f 0) (f 1) (<i> f i 0) (<i> f i 1) :=
Cube.lam (λ (x : interval_cube 1), product.elim f x)

def const {α : Sort u} (a : α) :
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
def and {α : Sort u} {a b : α}
  (p : a ⇝ b) : Square (λ _, a) (λ i, p # i) (<i> a) p :=
lam (λ i j, p # i ∧ j)

def or {α : Sort u} {a b : α}
  (p : a ⇝ b) : Square (λ i, p # i) (λ _, b) p (<i> b) :=
lam (λ i j, p # i ∨ j)

/-
def Square.compute {α : Sort u} {m n : I → α}
  {o : m 0 ⇝ n 0} {p : m 1 ⇝ n 1}
  (s : Square m n o p) : Π i, m i ⇝ n i
-/

end ground_zero.cubical.Square