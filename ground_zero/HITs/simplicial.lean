import ground_zero.HITs.truncation
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
| (n + 1) := coproduct ground_zero.types.unit.{1} (iterated_unit n)

def filled_simplex (n : ℕ) := ∥iterated_unit n∥

inductive simplex.core : ℕ → Type
| base {n : ℕ} : simplex.core (n + 1)
| lift {n : ℕ} : simplex.core n → simplex.core (n + 1)

inductive simplex.rel : Π n, simplex.core n → simplex.core n → Prop
| mk {n : ℕ} (x : simplex.core n) :
  simplex.rel (n + 1) simplex.core.base (simplex.core.lift x)

def simplex (n : ℕ) := quot (simplex.rel n)

end ground_zero.HITs