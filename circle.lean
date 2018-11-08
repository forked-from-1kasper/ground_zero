import ground_zero.suspension ground_zero.structures
import ground_zero.interval ground_zero.product
open ground_zero.structures (hset)

namespace ground_zero

universes u v

notation [parsing_only] `S⁻¹` := empty
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
    intro u, induction u },
  { intro x, simp, induction x,
    repeat { trivial } }
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

  notation u ` =[` p `] ` v := equiv.subst p u = v

  def ind {β : S¹ → Type u} (b : β base)
    (ℓ : b =[loop] b) : Π (x : S¹), β x :=
  suspension.ind b (seg₁ ▸ b)
    (begin
      intro x,
      have p := heq.from_homo (support.truncation ℓ⁻¹),
      refine heq.trans p _,
      admit
    end)

  def loops := Ω[1], ⟨S¹, base⟩

  def succ (l : loops) : loops := l ⬝ loop
  def pred (l : loops) : loops := l ⬝ loop⁻¹

  def zero := eq.refl base
  def one := succ zero
  def two := succ one
  def three := succ two
  def fourth := succ three

  inductive int
  | pos : ℕ → int
  | zero
  | neg : ℕ → int
  /-
    pos 1 is    2
    pos 0 is    1
    zero is     0
    neg 0 is   −1
    neg 1 is   −2
  -/

  def pos : ℕ → loops
  | 0 := loop
  | (n+1) := pos n ⬝ loop

  def neg : ℕ → loops
  | 0 := loop
  | (n+1) := pos n ⬝ loop⁻¹

  def code : int → loops
  | (int.pos n) := pos n
  | int.zero := eq.refl base
  | (int.neg n) := neg n

  example : code (int.pos 2) = loop ⬝ loop ⬝ loop :=
  by reflexivity
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

  abbreviation prod {α : Type u} {β : Type v} {a b : α} {c d : β}
    (p : a = b :> α) (q : c = d :> β) :
    ⟨a, c⟩ = ⟨b, d⟩ :> α × β :=
  product.construction a b c d p q

  -- poloidal and toroidal directions
  def p : b = b :> T² := prod (eq.refl circle.base) circle.loop
  def q : b = b :> T² := prod circle.loop (eq.refl circle.base)

  def Φ {π : Type u} {x x' y y' : π}
    (α : x = x' :> π) (β : y = y' :> π) :
    prod (eq.refl x) β ⬝ prod α (eq.refl y') =
    prod α (eq.refl y) ⬝ prod (eq.refl x') β :> _ :=
  begin induction α, induction β, trivial end

  def t : p ⬝ q = q ⬝ p :> b = b :> T² :=
  Φ circle.loop circle.loop
end torus

end ground_zero