import ground_zero.suspension ground_zero.eq ground_zero.equiv
import ground_zero.structures
open ground_zero.structures (hset)

namespace ground_zero

universe u

notation `S⁻¹` := empty
notation `S⁰` := bool

theorem up_dim : ∑S⁻¹ ≃ S⁰ :=
let f : ∑S⁻¹ → S⁰ :=
suspension.rec ff tt (λ (e : empty), begin induction e end) in
let g : S⁰ → ∑S⁻¹ :=
λ b, match b with
  ff := suspension.north
| tt := suspension.south
end in begin
  existsi f, split; existsi g,
  admit, admit
end

def circle := ∑S⁰
notation `S¹` := circle

namespace circle
  -- https://github.com/leanprover/lean2/blob/master/hott/homotopy/circle.hlean
  def base₁ : S¹ := suspension.north
  def base₂ : S¹ := suspension.south

  def seg₁ : base₁ = base₂ :> S¹ := suspension.merid ff
  def seg₂ : base₁ = base₂ :> S¹ := suspension.merid tt

  def base : S¹ := base₁
  def loop : base = base :> S¹ := seg₂ ⬝ seg₁⁻¹

  def rec {β : Type u} (b : β) (ℓ : b = b :> β) : S¹ → β :=
  suspension.rec b b (λ _, ℓ)
end circle

end ground_zero