import ground_zero.suspension ground_zero.eq ground_zero.equiv
import ground_zero.structures
open ground_zero.structures (hset)

namespace ground_zero

universe u

notation `S⁻¹` := empty
notation [parsing_only] `S⁰` := bool

theorem up_dim : ∑S⁻¹ ≃ S⁰ :=
let f : ∑S⁻¹ → S⁰ :=
suspension.rec ff tt (λ (e : empty), begin induction e end) in
let g : S⁰ → ∑S⁻¹ :=
λ b, match b with
  ff := suspension.north
| tt := suspension.south
end in begin
  existsi f, split; existsi g,
  { intro x, simp, admit },
  { intro x, simp, induction x,
    repeat { trivial } }
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

  def ind {β : S¹ → Type u} (b : β base)
    (ℓ : b == seg₁ ▸ b) : Π (x : S¹), β x :=
  suspension.ind b (seg₁ ▸ b) (λ _, ℓ)
end circle

namespace ncircle
  def S : ℕ → Sort _
  | 0 := S¹
  | (n+1) := ∑(S n)

  notation `S²` := S 2
end ncircle

end ground_zero