import ground_zero.HITs.pushout ground_zero.HITs.interval
import ground_zero.types.integers
open ground_zero.types

/-
  Homotopical reals R.
  * HoTT 8.1.5
-/
namespace ground_zero.HITs
universe u

local notation ℤ := integers

inductive reals.rel : ℤ → ℤ → Prop
| glue (x : ℤ) : reals.rel x (integers.succ x)
def reals := quot reals.rel
notation `R` := reals

namespace reals
  def elem : ℤ → R := quot.mk rel
  def glue (z : ℤ) : elem z = elem (integers.succ z) :> R :=
  ground_zero.support.inclusion (quot.sound $ rel.glue z)

  def ind {π : R → Sort u} (cz : Π x, π (elem x))
    (sz : Π z, cz z =[glue z] cz (integers.succ z))
    (u : R) : π u := begin
    refine quot.hrec_on u _ _,
    exact cz, intros x y p, cases p,
    refine ground_zero.types.eq.rec _
      (equiv.subst_from_pathover (sz x)),
    apply ground_zero.types.heq.eq_subst_heq
  end

  def rec {π : Sort u} (cz : ℤ → π)
    (sz : Π z, cz z = cz (integers.succ z) :> π) : R → π :=
  ind cz (λ x, dep_path.pathover_of_eq (glue x) (sz x))

  def positive : Π n, elem 0 = elem (integers.pos n) :> R
  | 0 := ground_zero.types.eq.refl (elem 0)
  | (n + 1) := positive n ⬝ glue (integers.pos n)

  def negative : Π n, elem 0 = elem (integers.neg n) :> R
  | 0 := (glue (integers.neg 0))⁻¹
  | (n + 1) := negative n ⬝ (glue $ integers.neg (n + 1))⁻¹

  def center : Π z, elem 0 = elem z :> R
  | (integers.pos n) := positive n
  | (integers.neg n) := negative n

  def vect (u v : ℤ) : elem u = elem v :> R :=
  (center u)⁻¹ ⬝ center v
end reals

namespace geometry
  notation `R²` := R × R
end geometry

end ground_zero.HITs