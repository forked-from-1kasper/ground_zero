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

def neq {α : Type u} (a b : α) : Type u := a = b → (𝟎 : Type)

def fin : ℕ → Type
| 0 := empty
| (n + 1) := coproduct ground_zero.types.unit.{0} (fin n)

def filled  (n : ℕ) := ∥fin n∥

inductive coupling.rel (α : Type u) : α → α → Type u
| mk {} : Π (a b : α), neq a b → coupling.rel a b

def coupling (α : Type u) := graph (generalized.rel α)

def simplex (n : ℕ) := coupling (fin n)
def simplex.elem {n : ℕ} : fin n → simplex n := graph.elem

end ground_zero.HITs