import ground_zero.HITs.circle ground_zero.theorems.fibration
open ground_zero ground_zero.HITs

hott theory

namespace ground_zero.theorems.hopf

namespace real
  -- real (S⁰ ↪ S¹ ↠ S¹)
  def family : S¹ → Type := circle.rec S⁰ (ua ua.neg_bool_equiv)
  def total : Type := Σ' x, family x

  def inj (x : S⁰) : total := ⟨circle.base, x⟩

  abbreviation map : total → S¹ := psigma.fst
end real

end ground_zero.theorems.hopf