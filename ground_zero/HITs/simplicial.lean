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

def fin : ℕ → Type
| 0 := empty
| (n + 1) := coproduct ground_zero.types.unit.{0} (fin n)

def filled  (n : ℕ) := ∥fin n∥

def simplex (n : ℕ) := generalized (fin n)
def simplex.elem {n : ℕ} : fin n → simplex n := generalized.incl

end ground_zero.HITs