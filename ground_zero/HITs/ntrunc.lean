import ground_zero.HITs.circle

/-
  n-truncation constructed using “hub and spokes”
  * HoTT 7.3
-/

open ground_zero.structures
open ground_zero.HITs.ncircle (S)

namespace ground_zero
namespace HITs

local infix ` = ` := eq

inductive {u} ntrunc.core (α : Sort u) : ℕ → Sort (u + 1)
| elem {n : ℕ} : α → ntrunc.core n
| hub {n : ℕ} : (S (n + 1) → ntrunc.core n) → ntrunc.core n

inductive {u} ntrunc.rel (α : Sort u) (n : ℕ) :
  ntrunc.core α n → ntrunc.core α n → Prop
| spoke (r : S (n + 1) → ntrunc.core α n) (x : S (n + 1)) :
  ntrunc.rel (r x) (ntrunc.core.hub r)

def {u} ntrunc (n : ℕ) (α : Sort u) :=
@quot (ntrunc.core α n) (ntrunc.rel α n)

def strunc := ntrunc 1
notation `∥` α `∥₀` := strunc α

namespace strunc
  universe u

  def elem {α : Sort u} (a : α) : ∥α∥₀ :=
  quot.mk (ntrunc.rel α 1) (core.elem a)
end strunc

namespace ntrunc
  universe u

  def elem {α : Sort u} {n : ℕ} (a : α) :
    ntrunc n α :=
  quot.mk (rel α n) (core.elem a)

  theorem truncation_is_correct {α : Sort u} {n : ℕ} :
    is_n_type (ntrunc n α) (n_to_level n) := begin
    admit
  end
end ntrunc

end HITs
end ground_zero