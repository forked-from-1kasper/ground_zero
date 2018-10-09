import ground_zero.suspension ground_zero.eq

namespace ground_zero

def circle := ∑bool
notation `S¹` := circle

namespace circle
  -- https://github.com/leanprover/lean2/blob/master/hott/homotopy/circle.hlean
  def base₁ : S¹ := suspension.north
  def base₂ : S¹ := suspension.south

  def seg₁ : base₁ = base₂ := suspension.merid ff
  def seg₂ : base₁ = base₂ := suspension.merid tt

  def base : S¹ := base₁
  def loop : base = base := seg₂ ⬝ seg₁⁻¹
end circle

end ground_zero