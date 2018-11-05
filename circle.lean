import ground_zero.suspension ground_zero.structures
import ground_zero.interval
open ground_zero.structures (hset)

namespace ground_zero

universes u v

notation `S⁻¹` := empty
notation [parsing_only] `S⁰` := bool

local infix ` = ` := eq

theorem up_dim : ∑S⁻¹ ≃ S⁰ :=
let f : ∑S⁻¹ → S⁰ :=
suspension.rec ff tt (λ (e : empty), begin induction e end) in
let g : S⁰ → ∑S⁻¹ :=
λ b, match b with
  ff := suspension.north
| tt := suspension.south
end in begin
  existsi f, split; existsi g,
  { intro x, simp,
    refine @suspension.ind _
      (λ x, g (f x) = x :> _)
      (by reflexivity)
      (by reflexivity)
      _ x,
    intro x, induction x },
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

  notation u ` =[` p `] ` v := equiv.subst p u = v

  def ind {β : S¹ → Type u} (b : β base)
    (ℓ : b =[loop] b) : Π (x : S¹), β x :=
  suspension.ind b (seg₁ ▸ b)
    (begin
      intro x,
      have p := heq.from_homo (support.to_builtin ℓ⁻¹),
      refine heq.trans p _,
      admit
    end)
end circle

namespace ncircle
  def S : ℕ → Sort _
  | 0 := S⁰
  | (n+1) := ∑(S n)

  notation `S²` := S 2
end ncircle

def torus := S¹ × S¹
notation `T²` := torus

namespace torus
  def b : T² := ⟨circle.base, circle.base⟩

  def inj₁ : S¹ → T² := product.intro circle.base
  def inj₂ : S¹ → T² := function.swap product.intro circle.base

  -- poloidal and toroidal directions
  def p : b = b :> T² := inj₁ # circle.loop
  def q : b = b :> T² :=
  let path := inj₂ # circle.loop in path

  /-
  def q : b = b :> T² := inj₂ # circle.loop

  unexpected argument at application
    eq.map inj₂
  given argument
    inj₂
  expected argument
    product.intro circle.base

  WTF?
  -/

  def t : p ⬝ q = q ⬝ p :> b = b :> T² := sorry
end torus

end ground_zero