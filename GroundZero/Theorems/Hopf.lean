import GroundZero.Theorems.Fibration
import GroundZero.HITs.Circle

open GroundZero GroundZero.HITs GroundZero.Types.Equiv
open GroundZero.Structures GroundZero.Types

namespace GroundZero.Theorems.Hopf

namespace Real
  -- Real (S⁰ ↪ S¹ ↠ S¹)
  def family : S¹ → Type := Circle.rec S⁰ (ua ua.negBoolEquiv)
  def total : Type := Σ x, family x

  def inj (x : S⁰) : total := ⟨Circle.base, x⟩

  def map : total → S¹ := Sigma.fst

  def μ₁ : total := ⟨Circle.base, false⟩
  def μ₂ : total := ⟨Circle.base, true⟩

  noncomputable hott def family.transport₁ : transport family Circle.loop ~ not :=
  begin
    intro b; transitivity; apply transportToTransportconst;
    transitivity; apply Id.map (transportconst · b);
    apply Circle.recβrule₂; apply ua.transportRule
  end

  noncomputable hott def family.transport₂ : transport family Circle.loop⁻¹ ~ not :=
  begin
    intro b; transitivity; apply transportToTransportconst;
    transitivity; apply Id.map (transportconst · b);
    transitivity; apply Id.mapInv; apply Id.map; apply Circle.recβrule₂;
    transitivity; apply transportconstOverInv; apply ua.transportInvRule
  end

  noncomputable hott def ρ₁ : μ₁ = μ₂ :=
  Sigma.prod Circle.loop (family.transport₁ false)

  noncomputable hott def ρ₂ : μ₁ = μ₂ :=
  Sigma.prod Circle.loop⁻¹ (family.transport₂ false)

  noncomputable hott def ret : S¹ → total :=
  Suspension.rec μ₁ μ₂ (λ | false => ρ₁ | true => ρ₂)
end Real

namespace Complex
  -- Complex (S¹ ↪ S³ ↠ S²)
  hott def family : S² → Type := Suspension.rec S¹ S¹ (ua ∘ Circle.μₑ)
end Complex

end GroundZero.Theorems.Hopf