import ground_zero.HITs.circle ground_zero.theorems.fibration
open ground_zero ground_zero.HITs ground_zero.types.equiv ground_zero.types

hott theory

namespace ground_zero.theorems.hopf

namespace real
  -- real (S⁰ ↪ S¹ ↠ S¹)
  def family : S¹ → Type := circle.rec S⁰ (ua ua.neg_bool_equiv)
  def total : Type := Σ x, family x

  def inj (x : S⁰) : total := ⟨circle.base, x⟩

  abbreviation map : total → S¹ := sigma.fst
end real

namespace complex
  -- complex (S¹ ↪ S³ ↠ S²)
  def family : S² → Type := suspension.rec S¹ S¹ (ua ∘ circle.μₑ)
end complex

end ground_zero.theorems.hopf