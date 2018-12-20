import ground_zero.HITs.circle

namespace ground_zero.HITs
local notation `ℤ` := circle.int

inductive reals.rel : ℤ → ℤ → Prop
| glue (x : ℤ) : reals.rel x (circle.int.succ x)
def reals := quot reals.rel
notation `ℝ` := reals

namespace reals

def elem : ℤ → ℝ := quot.mk rel
def glue (z : ℤ) : elem z = elem (circle.int.succ z) :> ℝ :=
ground_zero.support.inclusion (quot.sound $ rel.glue z)

end reals

end ground_zero.HITs