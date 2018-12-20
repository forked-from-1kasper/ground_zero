import ground_zero.HITs.int ground_zero.support

namespace ground_zero.HITs

inductive reals.rel : ℤ → ℤ → Prop
| glue (x : ℤ) : reals.rel x (x + 1)
def reals := quot reals.rel
notation `ℝ` := reals

namespace reals

def elem : ℤ → ℝ := quot.mk rel
def glue (z : ℤ) : elem z = elem (z + 1) :> ℝ :=
ground_zero.support.inclusion (quot.sound $ rel.glue z)

end reals

end ground_zero.HITs