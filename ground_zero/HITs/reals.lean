import ground_zero.HITs.int ground_zero.HITs.pushout
import ground_zero.HITs.interval

namespace ground_zero.HITs
universe u

inductive reals.rel : int → int → Prop
| glue (x : int) : reals.rel x (x + 1)
def reals := quot reals.rel
notation `ℝ` := reals

namespace reals

def elem : int → ℝ := quot.mk rel
def glue (z : int) : elem z = elem (z + 1) :> ℝ :=
ground_zero.support.inclusion (quot.sound $ rel.glue z)

def ind {π : ℝ → Sort u} (cz : Π (x : int), π (elem x))
  (sz : Π (z : int), cz z =[glue z] cz (z + 1))
  (u : ℝ) : π u := begin
  refine quot.hrec_on u _ _,
  exact cz, intros x y p, cases p,
  refine ground_zero.types.eq.rec _ (sz x),
  apply ground_zero.types.heq.eq_subst_heq
end

def rec {π : Sort u} (cz : int → π)
  (sz : Π (z : int), cz z = cz (z + 1) :> π) : ℝ → π :=
ind cz (λ x, pushout.pathover_of_eq (glue x) (sz x))

end reals

end ground_zero.HITs