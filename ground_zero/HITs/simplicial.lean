import ground_zero.HITs.merely
open ground_zero.types
open ground_zero.types.eq (renaming rfl -> idp)

/-
  * Filled simplex.
  * Simplex.
-/

hott theory

namespace ground_zero.HITs
universes u v w

def iterated_unit : ℕ → Type
| 0 := empty
| (n + 1) := coproduct ground_zero.types.unit.{0} (iterated_unit n)

def filled_simplex (n : ℕ) := ∥iterated_unit n∥

inductive simplex.core : ℕ → Type
| base {n : ℕ} : simplex.core (n + 1)
| lift {n : ℕ} : simplex.core n → simplex.core (n + 1)

inductive simplex.rel : Π n, simplex.core n → simplex.core n → Type
| mk {n : ℕ} (x : simplex.core n) :
  simplex.rel (n + 1) simplex.core.base (simplex.core.lift x)

def simplex (n : ℕ) := graph (simplex.rel n)

@[hott] def simplex.base {n : ℕ} : simplex (n + 1) :=
graph.elem (@simplex.core.base n)

@[hott] def simplex.lift {n : ℕ} : simplex n → simplex (n + 1) :=
graph.rec (graph.elem ∘ simplex.core.lift) (begin
  intros x y H, induction H with n x,
  transitivity, { symmetry, apply graph.line, apply simplex.rel.mk },
  apply graph.line, apply simplex.rel.mk
end)

end ground_zero.HITs