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

  def seg₁ : base₁ = base₂ := suspension.merid ff
  def seg₂ : base₁ = base₂ := suspension.merid tt

  def base : S¹ := base₁
  def loop : base = base := seg₂ ⬝ seg₁⁻¹

  def rec {β : Type u} (b : β) (ℓ : b = b) : S¹ → β :=
  suspension.rec b b (λ _, ℓ)

  theorem triviality_implies_set (h : loop = eq.refl base) : hset Type := begin
    let err : Π (b : Type) (p : b = b), p = eq.refl b :=
    λ b p, eq.map (eq.map (rec b p)) h,
    apply structures.hset.mk, intros α β p q,
    induction q, apply err
  end
end circle

end ground_zero