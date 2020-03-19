import ground_zero.HITs.suspension
import ground_zero.types.integer ground_zero.theorems.nat
open ground_zero.types.equiv (subst transport)
open ground_zero.types.eq
open ground_zero.structures (hset)
open ground_zero.types

/-
  Circle S¹ as Higher Inductive Type.
  * HoTT 6.4

  π₁(S¹) = ℤ proof.
  * HoTT 8.1
-/

hott theory

namespace ground_zero
namespace HITs

universes u v w

notation [parsing_only] `S⁻¹` := empty
notation [parsing_only] `S⁰` := bool

theorem up_dim : ∑S⁻¹ ≃ S⁰ :=
let f : ∑S⁻¹ → S⁰ :=
suspension.rec ff tt (λ e, by induction e) in
let g : S⁰ → ∑S⁻¹ :=
λ b, match b with
  ff := suspension.north
| tt := suspension.south
end in begin
  existsi f, split; existsi g,
  { intro x,
    refine @suspension.ind _
      (λ x, g (f x) = x)
      _ _ _ x,
    refl, refl,
    intro u, induction u },
  { intro x, induction x,
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

  def halfway : base = base :=
  interval.lam (λ i, interval.elim loop (i ∧ (interval.neg i)))

  def rec {β : Type u} (b : β) (ℓ : b = b) : S¹ → β :=
  suspension.rec b b (λ b, bool.cases_on b rfl ℓ)

  def recβrule₁ {β : Type u} (b : β) (ℓ : b = b) :
    rec b ℓ base = b := rfl

  def map_functoriality {α : Type u} {β : Type v}
    {a b c : α} (f : α → β) {p : a = b} {q : b = c} :
    f # (p ⬝ q) = (f # p) ⬝ (f # q) :=
  begin induction p, trivial end

  def map_symm {α : Type u} {β : Type v}
    {a b : α} (f : α → β) {p : a = b} :
    f # p⁻¹ = (f # p)⁻¹ :=
  begin induction p, reflexivity end

  def idmap {α : Type u} {a b : α} (p : a = b) : p = id # p :=
  begin induction p, trivial end

  noncomputable def recβrule₂ {β : Type u} (b : β) (ℓ : b = b) := calc
    rec b ℓ # loop = rec b ℓ # seg₂ ⬝ rec b ℓ # seg₁⁻¹ : by apply map_functoriality
               ... = rec b ℓ # seg₂ ⬝ (rec b ℓ # seg₁)⁻¹ :
                     begin apply eq.map, apply eq.map_inv end
               ... = ℓ ⬝ (rec b ℓ # seg₁)⁻¹ :
                     begin apply eq.map (⬝ (rec b ℓ # seg₁)⁻¹),
                           apply suspension.recβrule end
               ... = ℓ ⬝ eq.rfl⁻¹ :
                     begin apply eq.map, apply eq.map types.eq.symm,
                           apply suspension.recβrule end
               ... = ℓ : by apply eq.refl_right

  def ind {β : S¹ → Type u} (b : β base)
    (ℓ : b =[loop] b) : Π (x : S¹), β x :=
  ind₂ b (types.equiv.subst seg₁ b)
    types.eq.rfl
    (begin
      have p := types.equiv.subst_comp seg₂ seg₁⁻¹ b,
      have q := (λ p, subst p (subst seg₂ b)) #
                (types.eq.inv_comp seg₁),
      apply types.eq.trans, exact q⁻¹, transitivity,
      exact types.equiv.subst_comp seg₁⁻¹ seg₁ (subst seg₂ b),
      symmetry, exact subst seg₁ # (ℓ⁻¹ ⬝ p)
    end)

  instance pointed_circle : types.eq.dotted S¹ := ⟨base⟩

  noncomputable def loop_eq_refl_impls_uip {α : Type u}
    (H : loop = idp base) : structures.K α := begin
    intros a p, transitivity,
    symmetry, apply circle.recβrule₂ a p,
    change _ = (rec a p) # (idp base),
    apply eq.map, assumption
  end

  noncomputable def loop_neq_refl : ¬(loop = idp base) := begin
    intro h, apply ua.universe_not_a_set,
    intros α β p q, apply (structures.K_iff_set Type).left,
    apply loop_eq_refl_impls_uip, assumption
  end

  namespace map
    def trivial    : S¹ → S¹ := rec base (idp base)
    def nontrivial : S¹ → S¹ := rec base loop

    noncomputable def trivial_not_hmtpy : ¬(trivial = id) := begin
      intro p, apply loop_neq_refl,
      transitivity, apply idmap,
      apply transport (λ f, f # loop = idp (f base)) p,
      apply circle.recβrule₂
    end

    noncomputable def trivial_hmtpy : trivial ~ (λ _, base) := begin
      intro x, apply ind _ _ x,
      refl, apply types.eq.trans, apply equiv.transport_over_contr_map,
      transitivity, apply eq.map (⬝ idp base), apply eq.map_inv,
      transitivity, apply eq.map (⬝ idp base), apply eq.map,
      apply recβrule₂, trivial
    end

    noncomputable def nontrivial_hmtpy : nontrivial ~ id := begin
      intro x, apply ind _ _ x,
      refl, apply types.eq.trans, apply equiv.transport_over_involution,
      transitivity, apply eq.map (λ p, p ⬝ idp base ⬝ loop),
      transitivity, apply eq.map_inv, apply eq.map, apply recβrule₂,
      transitivity, apply eq.map (⬝ loop), apply eq.refl_right,
      apply types.eq.inv_comp
    end

    noncomputable def nontrivial_not_hmtpy : ¬(nontrivial = (λ _, base)) :=
    λ p, trivial_not_hmtpy (interval.funext trivial_hmtpy ⬝ p⁻¹ ⬝
                            interval.funext nontrivial_hmtpy)
  end map

  def succ (l : Ω¹(S¹)) : Ω¹(S¹) := l ⬝ loop
  def pred (l : Ω¹(S¹)) : Ω¹(S¹) := l ⬝ loop⁻¹

  def zero   := idp base
  def one    := succ zero
  def two    := succ one
  def three  := succ two
  def fourth := succ three

  def helix : S¹ → Type :=
  rec integer (ua integer.succ_equiv)

  def pos : ℕ → Ω¹(S¹)
  |    0    := idp base
  | (n + 1) := pos n ⬝ loop

  def neg : ℕ → Ω¹(S¹)
  |    0    := loop⁻¹
  | (n + 1) := neg n ⬝ loop⁻¹

  def power : integer → Ω¹(S¹)
  | (integer.pos n) := pos n
  | (integer.neg n) := neg n

  def encode (x : S¹) (p : base = x) : helix x :=
  transport helix p (integer.pos 0)

  example : power (integer.pos 2) = loop ⬝ loop :=
  by reflexivity

  def winding (x : base = base) : integer :=
  @transport S¹ helix base base x (integer.pos 0)

  noncomputable def transport_there (x : integer) := calc
    transport helix loop x = @transport Type id (helix base) (helix base)
                               (@eq.map S¹ Type base base helix loop) x :
                             by apply types.equiv.transport_comp id
                       ... = @transport Type id (helix base) (helix base)
                               (ua integer.succ_equiv) x :
                             begin apply types.equiv.homotopy.eq,
                                   apply eq.map, apply recβrule₂ end
                       ... = integer.succ x : by apply ua.transport_rule

  noncomputable def transport_back (x : integer) := calc
    transport helix loop⁻¹ x = @transport Type id (helix base) (helix base)
                                 (@eq.map S¹ Type base base helix loop⁻¹) x :
                               by apply types.equiv.transport_comp id
                         ... = @transport Type id (helix base) (helix base)
                                 (ua integer.succ_equiv)⁻¹ x :
                               begin apply types.equiv.homotopy.eq, apply eq.map,
                                     transitivity, apply eq.map_inv,
                                     apply eq.map, apply recβrule₂ end
                         ... = @equiv.subst_inv Type id (helix base) (helix base)
                                 (ua integer.succ_equiv) x :
                               by apply types.equiv.subst_over_inv_path
                         ... = integer.succ_equiv.backward x :
                               by apply ua.transport_inv_rule
                         ... = integer.pred x : by reflexivity

  noncomputable def decode : Π (x : S¹), helix x → base = x :=
  @ind (λ x, helix x → base = x) power (begin
    apply HITs.interval.funext, intro x,
    apply types.equiv.homotopy.eq, transitivity,
    exact types.equiv.transport_characterization power loop,
    apply HITs.interval.funext, intro n,
    simp, transitivity,
    apply types.equiv.transport_composition, transitivity,
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

  noncomputable def decode_encode (x : S¹) (p : base = x) :
    decode x (encode x p) = p :=
  begin induction p, reflexivity end

  noncomputable def coproduct_set {α β : Type}
    (f : hset α) (g : hset β) : hset (α + β)
  | (coproduct.inl x) (coproduct.inl y) :=
    transport structures.prop (ua $ @coproduct.inl.inj' α β x y)⁻¹ f
  | (coproduct.inl x) (coproduct.inr y) :=
    transport structures.prop (ua $ @types.coproduct.inl.inl_inr α β x y)⁻¹
              structures.empty_is_prop
  | (coproduct.inr x) (coproduct.inl y) :=
    transport structures.prop (ua $ @types.coproduct.inr.inr_inl α β x y)⁻¹
              structures.empty_is_prop
  | (coproduct.inr x) (coproduct.inr y) :=
    transport structures.prop (ua $ @coproduct.inr.inj' α β x y)⁻¹ g

  noncomputable def integer_is_set : ground_zero.structures.hset integer :=
  begin apply coproduct_set; apply theorems.nat.nat_is_set end

  noncomputable def encode_decode (x : S¹) (c : helix x) :
    encode x (decode x c) = c :=
  @ind (λ x, Π c, encode x (decode x c) = c)
    (begin
      clear c, clear x,
      intro c, induction c,
      { induction c with c ih,
        { reflexivity },
        { transitivity, apply equiv.subst_over_path_comp,
          transitivity, apply transport_there,
          transitivity, apply eq.map, apply ih,
          reflexivity } },
      { induction c with c ih,
        { apply transport_back },
        { transitivity, apply equiv.subst_over_path_comp,
          transitivity, apply transport_back,
          transitivity, apply eq.map, apply ih,
          reflexivity } }
    end)
    (begin
      apply interval.dfunext,
      intro x, apply integer_is_set
    end) x c

  noncomputable def family (x : S¹) : (base = x) ≃ helix x := begin
    existsi encode x, split; existsi decode x,
    apply decode_encode x, apply encode_decode x
  end

  local notation ℤ := integer

  noncomputable def fundamental_group : (Ω¹(S¹)) = ℤ :=
  ua (family base)

  noncomputable example : winding loop = integer.pos 1 :=
  transport_there (integer.pos 0)

  noncomputable example : winding loop⁻¹ = integer.neg 0 :=
  transport_back (integer.pos 0)

  def turn : Π (x : S¹), x = x :=
  circle.ind circle.loop (begin
    apply types.eq.trans, apply equiv.transport_inv_comp_comp,
    transitivity, apply eq.map (⬝ loop),
    apply eq.inv_comp, apply eq.refl_left
  end)

  def μ : S¹ → S¹ → S¹ :=
  circle.rec id (interval.funext turn)

  def inv : S¹ → S¹ :=
  circle.rec base loop⁻¹

  noncomputable def inv_inv (x : S¹) : inv (inv x) = x :=
  let invₚ := @eq.map S¹ S¹ base base (inv ∘ inv) in
  begin
    fapply circle.ind _ _ x; clear x,
    { reflexivity },
    { calc
        equiv.transport (λ x, inv (inv x) = x) loop eq.rfl =
                              invₚ loop⁻¹ ⬝ eq.rfl ⬝ loop :
      by apply equiv.transport_over_involution
        ... = invₚ loop⁻¹ ⬝ (eq.rfl ⬝ loop) :
      begin symmetry, apply eq.assoc end
        ... = inv # (inv # loop⁻¹) ⬝ loop :
      begin apply eq.map (⬝ loop), apply equiv.map_over_comp end
        ... = inv # (inv # loop)⁻¹ ⬝ loop :
      begin apply eq.map (⬝ loop),
            apply eq.map, apply eq.map_inv end
        ... = inv # loop⁻¹⁻¹ ⬝ loop :
      begin apply eq.map (⬝ loop),
            apply eq.map, apply eq.map,
            apply circle.recβrule₂ end
        ... = inv # loop ⬝ loop :
      begin apply eq.map (⬝ loop),
            apply eq.map, apply eq.inv_inv end
        ... = loop⁻¹ ⬝ loop :
      begin apply eq.map (⬝ loop), apply circle.recβrule₂ end
        ... = eq.rfl : by apply eq.inv_comp }
  end
end circle

namespace ncircle
  def S : ℕ → Type
  | 0 := S⁰
  | (n + 1) := ∑(S n)

  def lift : Π n, S n → S (n + 1)
  |    0    ff := suspension.north
  |    0    tt := suspension.south
  | (n + 1) x  := suspension.rec suspension.north suspension.south
                                 (λ _, suspension.merid x) x
end ncircle

namespace sphere
  notation `S²` := ncircle.S 2

  abbreviation base₁ : S² := suspension.north
  abbreviation base₂ : S² := suspension.south

  def loop : base₁ = base₂ := suspension.merid circle.base

  def surf_trans :=
  (λ p, suspension.merid p ⬝ loop⁻¹) # circle.loop

  abbreviation base : S² := suspension.north
  def surf : idp base = idp base :=
  (types.eq.comp_inv loop)⁻¹ ⬝ surf_trans ⬝ (types.eq.comp_inv loop)

  def rec {β : Type u} (b : β) (s : idp b = idp b) : S² → β :=
  suspension.rec b b (circle.rec (idp b) s)
end sphere

namespace glome
  notation `S³` := ncircle.S 3

  abbreviation base₁ : S³ := suspension.north
  abbreviation base₂ : S³ := suspension.south

  def loop : base₁ = base₂ := suspension.merid sphere.base

  abbreviation base : S³ := suspension.north
end glome

def torus := S¹ × S¹
notation `T²` := torus

namespace torus
  open types.product
  def b : T² := ⟨circle.base, circle.base⟩

  def inj₁ : S¹ → T² := prod.mk circle.base
  def inj₂ : S¹ → T² := function.swap prod.mk circle.base

  -- poloidal and toroidal directions
  def p : b = b :> T² := prod (idp circle.base) circle.loop
  def q : b = b :> T² := prod circle.loop (idp circle.base)

  def Φ {π : Type u} {x x' y y' : π}
    (α : x = x') (β : y = y') :
    prod (idp x) β ⬝ prod α (idp y') =
    prod α (idp y) ⬝ prod (idp x') β :=
  begin induction α, induction β, trivial end

  def t : p ⬝ q = q ⬝ p :> b = b :> T² :=
  Φ circle.loop circle.loop
end torus

inductive torus'.rel : I × I → I × I → Type
| top (x : I) : torus'.rel ⟨0, x⟩ ⟨1, x⟩
| bottom (x : I) : torus'.rel ⟨x, 0⟩ ⟨x, 1⟩

def torus' : Type := graph torus'.rel

namespace torus'
  open interval

  def a : torus' := graph.elem ⟨1, 0⟩
  def b : torus' := graph.elem ⟨0, 0⟩
  def c : torus' := graph.elem ⟨0, 1⟩
  def d : torus' := graph.elem ⟨1, 1⟩

  def top (x : I) : graph.elem ⟨0, x⟩ = graph.elem ⟨1, x⟩ :> torus' :=
  graph.line (rel.top x)

  def bottom (x : I) : graph.elem ⟨x, 0⟩ = graph.elem ⟨x, 1⟩ :> torus' :=
  graph.line (rel.bottom x)

  def p : b = b :> torus' :=
  graph.elem # (product.prod rfl   seg) ⬝
  graph.elem # (product.prod seg   rfl) ⬝
  graph.elem # (product.prod rfl   seg⁻¹) ⬝
  graph.elem # (product.prod seg⁻¹ rfl)

  def q : b = b :> torus' :=
  bottom 0 ⬝ top 1 ⬝ (bottom 1)⁻¹ ⬝ (top 0)⁻¹
end torus'

end HITs
end ground_zero