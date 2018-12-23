import ground_zero.HITs.suspension ground_zero.theorems.ua
open ground_zero.types.equiv (subst transport)
open ground_zero.types.eq (renaming refl -> idp)
open ground_zero.structures (hset)

namespace ground_zero
namespace HITs

universes u v

notation [parsing_only] `S⁻¹` := empty
notation [parsing_only] `S⁰` := bool

local infix ` = ` := types.eq

theorem up_dim : ∑S⁻¹ ≃ S⁰ :=
let f : ∑S⁻¹ → S⁰ :=
suspension.rec ff tt (λ e, by induction e) in
let g : S⁰ → ∑S⁻¹ :=
λ b, match b with
  ff := suspension.north
| tt := suspension.south
end in begin
  existsi f, split; existsi g,
  { intro x, simp,
    refine @suspension.ind _
      (λ x, g (f x) = x)
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

  def ind₂ {β : S¹ → Type u} (b₁ : β base₁) (b₂ : β base₂)
    (ℓ₁ : b₁ =[seg₁] b₂)
    (ℓ₂ : b₁ =[seg₂] b₂) : Π (x : S¹), β x :=
  suspension.ind b₁ b₂ (begin
    intro x, induction x,
    exact ℓ₁, exact ℓ₂
  end)

  def base : S¹ := base₁
  def loop : base = base := seg₂ ⬝ seg₁⁻¹

  def rec {β : Type u} (b : β) (ℓ : b = b) : S¹ → β :=
  suspension.rec b b (λ _, ℓ)

  def recβrule₁ {β : Type u} (b : β) (ℓ : b = b) :
    rec b ℓ base = b := types.eq.rfl

  def map_functoriality {α : Type u} {β : Type v}
    {a b c : α} (f : α → β) {p : a = b} {q : b = c} :
    f # (p ⬝ q) = (f # p) ⬝ (f # q) :=
  begin induction p, trivial end

  def map_symm {α : Type u} {β : Type v}
    {a b : α} (f : α → β) {p : a = b} :
    f # p⁻¹ = (f # p)⁻¹ :=
  begin induction p, reflexivity end

  def recβrule₂ {β : Type u} (b : β) (ℓ : b = b) :
    (rec b ℓ # loop) = ℓ := begin
    transitivity,
    apply map_functoriality (rec b ℓ),
    transitivity, apply types.eq.map, apply map_symm,
    admit
  end

  def ind {β : S¹ → Type u} (b : β base)
    (ℓ : b =[loop] b) : Π (x : S¹), β x :=
  ind₂ b (types.equiv.subst seg₁ b) types.eq.rfl
    (begin
      have p := types.equiv.subst_comp seg₂ seg₁⁻¹ b,
      have q := (λ p, subst p (subst seg₂ b)) #
                (types.eq.inv_comp seg₁),
      transitivity, exact q⁻¹, transitivity,
      exact types.equiv.subst_comp seg₁⁻¹ seg₁ (subst seg₂ b),
      symmetry, exact subst seg₁ # (ℓ⁻¹ ⬝ p)
    end)

  instance pointed_circle : types.eq.dotted S¹ := ⟨base⟩

  theorem natural_equivalence {α : Sort u} :
    (S¹ → α) ≃ (Σ' (x : α), x = x) := begin
    let f : (S¹ → α) → (Σ' (x : α), x = x) :=
    λ g, ⟨g base, g # loop⟩,
    let g : (Σ' (x : α), x = x) → (S¹ → α) :=
    λ p x, p.fst,
    existsi f, split; existsi g,
    { intro v, apply HITs.interval.funext,
      intro x, simp,
      admit },
    { intro v, induction v with p q,
      admit }
  end

  namespace going
    def trivial : S¹ → S¹ :=
    rec base (eq.refl base)

    def nontrivial : S¹ → S¹ :=
    rec base loop
  end going

  def succ (l : Ω¹(S¹)) : Ω¹(S¹) := l ⬝ loop
  def pred (l : Ω¹(S¹)) : Ω¹(S¹) := l ⬝ loop⁻¹

  def zero := idp base
  def one := succ zero
  def two := succ one
  def three := succ two
  def fourth := succ three

  /-
    +2 = pos 2
    +1 = pos 1
     0 = pos 0
    −1 = neg 0
    −2 = neg 1
  -/
  inductive int
  | pos : ℕ → int
  | neg : ℕ → int

  instance : has_zero int := ⟨int.pos 0⟩

  instance : has_repr int :=
  ⟨λ x, match x with
  | (int.pos n) := to_string n
  | (int.neg n) := "−" ++ to_string (n + 1)
  end⟩

  def int.auxsucc : ℕ → int
  | 0 := int.pos 0
  | (n + 1) := int.neg n

  def int.succ : int → int
  | (int.neg u) := int.auxsucc u
  | (int.pos v) := int.pos (v + 1)

  def int.auxpred : ℕ → int
  | 0 := int.neg 0
  | (n + 1) := int.pos n

  def int.pred : int → int
  | (int.neg u) := int.neg (u + 1)
  | (int.pos v) := int.auxpred v

  def int.equiv : int ≃ int := begin
    existsi int.succ, split; existsi int.pred,
    repeat {
      intro n, induction n,
      repeat { trivial },
      { induction n with n ih,
        repeat { trivial } }
    }
  end

  def helix : S¹ → Type :=
  rec int (ua int.equiv)

  def pos : ℕ → Ω¹(S¹)
  | 0 := types.eq.refl base
  | (n + 1) := pos n ⬝ loop

  def neg : ℕ → Ω¹(S¹)
  | 0 := loop⁻¹
  | (n + 1) := neg n ⬝ loop⁻¹

  def power : int → Ω¹(S¹)
  | (int.pos n) := pos n
  | (int.neg n) := neg n

  def encode (x : S¹) (p : base = x) : helix x :=
  types.equiv.transport helix p (int.pos 0)

  example : power (int.pos 2) = loop ⬝ loop :=
  by reflexivity

  abbreviation bicycle : helix base → int := id

  def winding (x : base = base) : int :=
  bicycle (transport helix x $ int.pos 0)

  def transport_characterization
    {α : Sort u} {β γ : α → Sort v} {a b : α}
    (f : β a → γ a) (p : a = b) :
    subst p f = transport γ p ∘ f ∘ transport β p⁻¹ :=
  begin induction p, reflexivity end

  def transport_to_comp
    {α : Sort u} {a b c : α}
    (p : a = b) (q : b = c) :
    transport (types.eq a) q p = p ⬝ q :=
  begin induction p, induction q, trivial end

  noncomputable def transport_there (x : int) :
    transport helix loop x = int.succ x := begin
    transitivity,
    apply types.equiv.transport_comp id helix loop,
    transitivity, apply types.equiv.homotopy.eq,
    apply types.eq.map subst, apply recβrule₂,
    apply ua.comp_rule
  end

  def transport_back (x : int) :
    transport helix loop⁻¹ x = int.pred x :=
  sorry

  def decode : Π (x : S¹), helix x → base = x :=
  @ind (λ x, helix x → base = x) power (begin
    apply HITs.interval.funext, intro x,
    apply types.equiv.homotopy.eq, transitivity,
    exact transport_characterization power loop,
    apply HITs.interval.funext, intro n,
    simp, transitivity,
    apply transport_to_comp, transitivity,
    apply types.eq.map (λ p, power p ⬝ loop),
    apply transport_back, induction n,
    -- :-(
    { induction n with n ih,
      { apply types.eq.inv_comp },
      { trivial } },
    { induction n with n ih,
      { symmetry, transitivity, symmetry,
        apply types.eq.refl_right, symmetry,
        transitivity, apply (types.eq.assoc loop⁻¹ loop⁻¹ loop)⁻¹,
        apply types.eq.map, apply types.eq.inv_comp },
      { transitivity,
        apply (types.eq.assoc (neg n ⬝ loop⁻¹) loop⁻¹ loop)⁻¹,
        transitivity, apply types.eq.map,
        apply types.eq.inv_comp, apply types.eq.refl_right } }
  end)

  noncomputable example : winding loop = int.pos 1 :=
  transport_there (int.pos 0)
end circle

namespace ncircle
  def S : ℕ → Sort _
  | 0 := S⁰
  | (n + 1) := ∑(S n)
end ncircle

namespace sphere
  notation `S²` := ncircle.S 2

  abbreviation base₁ : S² := suspension.north
  abbreviation base₂ : S² := suspension.south

  def loop : base₁ = base₂ := suspension.merid circle.base

  def surf_trans :=
  (λ p, suspension.merid p ⬝ loop⁻¹) # circle.loop

  abbreviation base : S² := suspension.north
  def surf : types.eq.refl base = types.eq.refl base :=
  (types.eq.comp_inv loop)⁻¹ ⬝ surf_trans ⬝ (types.eq.comp_inv loop)

  def rec {β : Type u} (b : β) (s : idp b = idp b) : S² → β :=
  suspension.rec b b (circle.rec (idp b) s)

  def ind {π : S² → Type u} (b : π base)
    (s : idp b =[λ p, b =[π, p] b, surf] idp b) : Π (x : S²), π x := begin
    refine suspension.ind b (subst loop b) _,
    intro x, refine circle.ind _ _ x,

    reflexivity,
    admit
  end
end sphere

def torus := S¹ × S¹
notation `T²` := torus

namespace torus
  open types.product
  def b : T² := ⟨circle.base, circle.base⟩

  def inj₁ : S¹ → T² := types.product.intro circle.base
  def inj₂ : S¹ → T² := function.swap types.product.intro circle.base

  -- poloidal and toroidal directions
  def p : b = b :> T² := prod (eq.refl circle.base) circle.loop
  def q : b = b :> T² := prod circle.loop (eq.refl circle.base)

  def Φ {π : Type u} {x x' y y' : π}
    (α : x = x') (β : y = y') :
    prod (idp x) β ⬝ prod α (idp y') =
    prod α (idp y) ⬝ prod (idp x') β :=
  begin induction α, induction β, trivial end

  def t : p ⬝ q = q ⬝ p :> b = b :> T² :=
  Φ circle.loop circle.loop

  def ind {π : T² → Type u} (b' : π b)
    (p' : b' =[p] b') (q' : b' =[q] b')
    (t' : p' ⬝' q' =[(λ r, subst r b' = b'), t] q' ⬝' p') :
    Π (x : T²), π x := begin
    intro x, cases x with poloidal toroidal,
    refine circle.ind _ _ poloidal,
    { refine circle.ind _ _ toroidal,
      exact b', admit },
    { admit }
  end
end torus

end HITs
end ground_zero