import ground_zero.cubical.path
open ground_zero.HITs (I)
open ground_zero.HITs.interval (i₀ i₁)
open ground_zero.cubical.cubes
open ground_zero

namespace ground_zero.cubical.square
universe u

def Square.lam {α : Sort u} (f : I → I → α) :
  Square (f i₀) (f i₁) (<i> f i i₀) (<i> f i i₁) :=
Cube.lam (λ (x : interval_cube 1), types.product.elim f x)

def Square.const {α : Sort u} (a : α) :
  Square (λ _, a) (λ _, a) (<i> a) (<i> a) :=
Square.lam (λ i j, a)

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
def Square.and {α : Sort u} {a b : α}
  (p : a ⇝ b) : Square (λ _, a) (λ i, p # i) (<i> a) p :=
Square.lam (λ i j, p # i ∧ j)

/-
def Square.compute {α : Sort u} {m n : I → α}
  {o : m i₀ ⇝ n i₀} {p : m i₁ ⇝ n i₁}
  (s : Square m n o p) : Π i, m i ⇝ n i
-/

end ground_zero.cubical.square