import ground_zero.circle

open ground_zero.structures
open ground_zero.ncircle (S)

namespace ground_zero

inductive {u} ntrunc.core (α : Sort u) : ℕ → Sort (u + 1)
| elem {n : ℕ} : α → ntrunc.core n
| hub {n : ℕ} : (S (n + 1) → ntrunc.core n) → ntrunc.core n

inductive {u} ntrunc.rel (α : Sort u) (n : ℕ) :
  ntrunc.core α n → ntrunc.core α n → Prop
| spoke (r : S (n + 1) → ntrunc.core α n) (x : S (n + 1)) :
  ntrunc.rel (r x) (ntrunc.core.hub r)

def {u} ntrunc (n : homotopy_level) (α : Sort u) :=
match n with
| homotopy_level.minus_two := ground_zero.unit
| homotopy_level.succ n :=
  @quot (ntrunc.core α (homotopy_level.succ n))
        (ntrunc.rel α (homotopy_level.succ n))
end

def strunc := ntrunc 0
notation `∥` α `∥₀` := strunc α

namespace ntrunc
  universe u

  def elem {α : Sort u} {n : homotopy_level} (a : α) :
    ntrunc n α :=
  match n with
  | homotopy_level.minus_two := ground_zero.unit.star
  | homotopy_level.succ n :=
    quot.mk (rel α (homotopy_level.succ n)) (core.elem a)
  end

  theorem truncation_is_correct {α : Sort u} {n : homotopy_level} :
    is_n_type (ntrunc n α) n := begin
    induction n with n ih,
    { unfold is_n_type, simp [ntrunc],
      apply contr.mk ground_zero.unit.star,
      intro x, induction x, reflexivity },
    admit
  end
end ntrunc

end ground_zero