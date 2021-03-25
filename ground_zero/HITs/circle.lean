import ground_zero.HITs.suspension ground_zero.theorems.prop
import ground_zero.types.integer

open ground_zero.structures (prop hset groupoid)
open ground_zero.types.equiv (subst transport)
open ground_zero.HITs.interval (happly)
open ground_zero.types.Id
open ground_zero.types
open combinator (S)

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

@[hott] theorem up_dim : ∑S⁻¹ ≃ S⁰ :=
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

namespace loop
  variables {α : Type u} {a : α}

  def pos (p : a = a) : ℕ → a = a
  |    0    := idp a
  | (n + 1) := pos n ⬝ p

  def neg (p : a = a) : ℕ → a = a
  |    0    := p⁻¹
  | (n + 1) := neg n ⬝ p⁻¹

  def power (p : a = a) : integer → a = a
  | (integer.pos n) := pos p n
  | (integer.neg n) := neg p n

  @[hott] def power_comp (p : a = a) (z : integer) :
    power p z ⬝ p = power p (integer.succ z) :=
  begin
    induction z, { trivial },
    { induction z with n ih,
      { apply Id.inv_comp },
      { transitivity, symmetry, apply Id.assoc,
        transitivity, apply Id.map (λ q, neg p n ⬝ q),
        apply Id.inv_comp, apply Id.refl_right } }
  end

  @[hott] def power_comp_pred (p : a = a) (z : integer) :
    power p z ⬝ p⁻¹ = power p (integer.pred z) :=
  begin
    induction z,
    { induction z with n ih,
      { reflexivity },
      { transitivity, symmetry, apply Id.assoc,
        transitivity, apply Id.map (λ q, pos p n ⬝ q),
        apply Id.comp_inv, apply Id.refl_right } },
    { trivial }
  end

  @[hott] def comp_power (p : a = a) (z : integer) :
    p ⬝ power p z = power p (integer.succ z) :=
  begin
    induction z,
    { induction z with n ih,
      { apply Id.refl_right },
      { transitivity, apply Id.assoc,
        transitivity, apply Id.map (⬝ p),
        exact ih, reflexivity } },
    { induction z with n ih,
      { apply Id.comp_inv },
      { transitivity, apply Id.assoc,
        symmetry, apply equiv.inv_comp_rewrite,
        symmetry, transitivity, apply ih,
        symmetry, apply power_comp } }
  end

  @[hott] def comp_power_pred (p : a = a) (z : integer) :
    p⁻¹ ⬝ power p z = power p (integer.pred z) :=
  begin
    induction z,
    { induction z with n ih,
      { apply Id.refl_right },
      { apply equiv.rewrite_comp,
        symmetry, apply comp_power } },
    { induction z with n ih,
      { reflexivity },
      { apply equiv.rewrite_comp,
        symmetry, apply comp_power } }
  end

  @[hott] def comp_power_comm (p : a = a) (z : integer) :
    p ⬝ power p z = power p z ⬝ p :=
  comp_power p z ⬝ (power_comp p z)⁻¹

  @[hott] def inv_comp_power_comm (p : a = a) (z : integer) :
    p⁻¹ ⬝ power p z = power p z ⬝ p⁻¹ :=
  comp_power_pred p z ⬝ (power_comp_pred p z)⁻¹

  @[hott] def power_comm (p : a = a) (x y : integer) :
    power p x ⬝ power p y = power p y ⬝ power p x :=
  begin
    fapply integer.indsp _ _ _ x; clear x,
    { symmetry, apply Id.refl_right },
    { intros x ih, transitivity, apply Id.map (⬝ power p y),
      symmetry, apply comp_power,
      transitivity, symmetry, apply Id.assoc,
      transitivity, apply Id.map, exact ih,
      transitivity, apply Id.assoc,
      transitivity, apply Id.map (⬝ power p x),
      apply comp_power_comm,
      transitivity, symmetry, apply Id.assoc,
      apply Id.map, apply comp_power },
    { intros x ih, transitivity, apply Id.map (⬝ power p y),
      symmetry, apply comp_power_pred,
      transitivity, symmetry, apply Id.assoc,
      transitivity, apply Id.map, exact ih,
      transitivity, apply Id.assoc,
      transitivity, apply Id.map (⬝ power p x),
      apply inv_comp_power_comm,
      transitivity, symmetry, apply Id.assoc,
      apply Id.map, apply comp_power_pred }
  end
end loop

namespace circle
  -- https://github.com/leanprover/lean2/blob/master/hott/homotopy/circle.hlean
  def base₁ : S¹ := suspension.north
  def base₂ : S¹ := suspension.south

  def seg₁ : base₁ = base₂ := suspension.merid ff
  def seg₂ : base₁ = base₂ := suspension.merid tt

  @[hott] def ind₂ {β : S¹ → Type u} (b₁ : β base₁) (b₂ : β base₂)
    (ℓ₁ : b₁ =[seg₁] b₂) (ℓ₂ : b₁ =[seg₂] b₂) : Π (x : S¹), β x :=
  suspension.ind b₁ b₂ (begin
    intro x, induction x,
    exact ℓ₁, exact ℓ₂
  end)

  def base : S¹ := base₁
  def loop : base = base := seg₂ ⬝ seg₁⁻¹

  def rec {β : Type u} (b : β) (ℓ : b = b) : S¹ → β :=
  suspension.rec b b (λ b, bool.cases_on b Id.refl ℓ)

  def recβrule₁ {β : Type u} (b : β) (ℓ : b = b) :
    rec b ℓ base = b := Id.refl

  @[hott] def map_symm {α : Type u} {β : Type v}
    {a b : α} (f : α → β) {p : a = b} :
    f # p⁻¹ = (f # p)⁻¹ :=
  begin induction p, reflexivity end

  @[hott] def idmap {α : Type u} {a b : α} (p : a = b) : p = id # p :=
  begin induction p, trivial end

  @[hott] noncomputable def recβrule₂ {β : Type u} (b : β) (ℓ : b = b) := calc
    rec b ℓ # loop = rec b ℓ # seg₂ ⬝ rec b ℓ # seg₁⁻¹ : by apply equiv.map_functoriality
               ... = rec b ℓ # seg₂ ⬝ (rec b ℓ # seg₁)⁻¹ :
                     begin apply Id.map, apply Id.map_inv end
               ... = ℓ ⬝ (rec b ℓ # seg₁)⁻¹ :
                     begin apply Id.map (⬝ (rec b ℓ # seg₁)⁻¹),
                           apply suspension.recβrule end
               ... = ℓ ⬝ Id.refl⁻¹ :
                     begin apply Id.map, apply Id.map types.Id.symm,
                           apply suspension.recβrule end
               ... = ℓ : by apply Id.refl_right

  @[hott] noncomputable def recβrule₃ {β : Type u} (b : β) (ℓ : b = b) :
    Π x, rec b ℓ # (suspension.merid x) = bool.cases_on x Id.refl ℓ :=
  by apply suspension.recβrule

  @[hott] def ind {β : S¹ → Type u} (b : β base)
    (ℓ : b =[loop] b) : Π (x : S¹), β x :=
  ind₂ b (types.equiv.subst seg₁ b) Id.refl
    (begin
      have p := types.equiv.subst_comp seg₂ seg₁⁻¹ b,
      have q := (λ p, subst p (subst seg₂ b)) #
                (types.Id.inv_comp seg₁),
      apply types.Id.trans, exact q⁻¹, transitivity,
      exact types.equiv.subst_comp seg₁⁻¹ seg₁ (subst seg₂ b),
      symmetry, exact subst seg₁ # (ℓ⁻¹ ⬝ p)
    end)

  @[hott] def indΩ {β : S¹ → Type u} (b : β base) (p : Π x, prop (β x)) : Π x, β x :=
  begin fapply ind, exact b, apply p end

  instance pointed_circle : types.Id.dotted S¹ := ⟨base⟩

  @[hott] noncomputable def loop_eq_refl_impls_uip {α : Type u}
    (H : loop = idp base) : structures.K α :=
  begin
    intros a p, transitivity,
    symmetry, apply circle.recβrule₂ a p,
    change _ = (rec a p) # (idp base),
    apply Id.map, assumption
  end

  @[hott] noncomputable def loop_neq_refl : ¬(loop = idp base) :=
  begin
    intro h, apply ua.universe_not_a_set,
    intros α β p q, apply (structures.K_iff_set Type).left,
    apply loop_eq_refl_impls_uip, assumption
  end

  namespace map
    def trivial    : S¹ → S¹ := rec base (idp base)
    def nontrivial : S¹ → S¹ := rec base loop

    @[hott] noncomputable def trivial_not_hmtpy : ¬(trivial = id) :=
    begin
      intro p, apply loop_neq_refl,
      transitivity, apply idmap,
      apply transport (λ f, f # loop = idp (f base)) p,
      apply circle.recβrule₂
    end

    @[hott] noncomputable def trivial_hmtpy : trivial ~ (λ _, base) :=
    begin
      intro x, apply ind _ _ x,
      refl, apply types.Id.trans, apply equiv.transport_over_contr_map,
      transitivity, apply Id.map (⬝ idp base), apply Id.map_inv,
      transitivity, apply Id.map (⬝ idp base), apply Id.map,
      apply recβrule₂, trivial
    end

    @[hott] noncomputable def nontrivial_hmtpy : nontrivial ~ id :=
    begin
      intro x, apply ind _ _ x,
      refl, apply types.Id.trans, apply equiv.transport_over_involution,
      transitivity, apply Id.map (λ p, p ⬝ idp base ⬝ loop),
      transitivity, apply Id.map_inv, apply Id.map, apply recβrule₂,
      transitivity, apply Id.map (⬝ loop), apply Id.refl_right,
      apply types.Id.inv_comp
    end

    @[hott] noncomputable def nontrivial_not_hmtpy : ¬(nontrivial = (λ _, base)) :=
    λ p, trivial_not_hmtpy (theorems.funext trivial_hmtpy ⬝ p⁻¹ ⬝
                            theorems.funext nontrivial_hmtpy)
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

  def power : integer → Ω¹(S¹) := loop.power loop

  def encode (x : S¹) (p : base = x) : helix x :=
  transport helix p (integer.pos 0)

  example : power (integer.pos 2) = loop ⬝ loop :=
  by reflexivity

  def winding : base = base → integer := encode base

  @[hott] noncomputable def transport_there (x : integer) := calc
    transport helix loop x = @transport Type id (helix base) (helix base)
                               (@Id.map S¹ Type base base helix loop) x :
                             by apply types.equiv.transport_comp id
                       ... = @transport Type id (helix base) (helix base)
                               (ua integer.succ_equiv) x :
                             begin apply types.equiv.homotopy.Id,
                                   apply Id.map, apply recβrule₂ end
                       ... = integer.succ x : by apply ua.transport_rule

  @[hott] noncomputable def transport_back (x : integer) := calc
    transport helix loop⁻¹ x = @transport Type id (helix base) (helix base)
                                 (@Id.map S¹ Type base base helix loop⁻¹) x :
                               by apply types.equiv.transport_comp id
                         ... = @transport Type id (helix base) (helix base)
                                 (ua integer.succ_equiv)⁻¹ x :
                               begin apply types.equiv.homotopy.Id, apply Id.map,
                                     transitivity, apply Id.map_inv,
                                     apply Id.map, apply recβrule₂ end
                         ... = @equiv.subst_inv Type id (helix base) (helix base)
                                 (ua integer.succ_equiv) x :
                               by apply types.equiv.subst_over_inv_path
                         ... = integer.succ_equiv.left x :
                               by apply ua.transport_inv_rule
                         ... = integer.pred x : by reflexivity

  @[hott] noncomputable def decode : Π (x : S¹), helix x → base = x :=
  @ind (λ x, helix x → base = x) power (begin
    apply theorems.funext, intro x,
    apply types.equiv.homotopy.Id, transitivity,
    exact types.equiv.transport_characterization power loop,
    apply theorems.funext, intro n, transitivity,
    apply types.equiv.transport_composition, transitivity,
    apply types.Id.map (λ z, power z ⬝ loop),
    apply transport_back, induction n,
    -- :-(
    { induction n with n ih,
      { apply types.Id.inv_comp },
      { trivial } },
    { induction n with n ih,
      { symmetry, transitivity, symmetry,
        apply types.Id.refl_right, symmetry,
        transitivity, apply (types.Id.assoc loop⁻¹ loop⁻¹ loop)⁻¹,
        apply types.Id.map, apply types.Id.inv_comp },
      { transitivity,
        apply (types.Id.assoc (@loop.neg S¹ _ loop n ⬝ loop⁻¹) loop⁻¹ loop)⁻¹,
        transitivity, apply types.Id.map,
        apply types.Id.inv_comp, apply types.Id.refl_right } }
  end)

  @[hott] noncomputable def decode_encode (x : S¹) (p : base = x) :
    decode x (encode x p) = p :=
  begin induction p, reflexivity end

  @[hott] noncomputable def power_of_winding : power ∘ winding ~ id :=
  decode_encode base

  @[hott] noncomputable def comm (x y : Ω¹(S¹)) : x ⬝ y = y ⬝ x :=
    equiv.bimap Id.trans (power_of_winding x)⁻¹ (power_of_winding y)⁻¹
  ⬝ loop.power_comm circle.loop (winding x) (winding y)
  ⬝ equiv.bimap Id.trans (power_of_winding y) (power_of_winding x)

  @[hott] noncomputable def encode_decode (x : S¹) (c : helix x) :
    encode x (decode x c) = c :=
  @ind (λ x, Π c, encode x (decode x c) = c)
    (begin
      clear c, clear x,
      intro c, induction c,
      { induction c with c ih,
        { reflexivity },
        { transitivity, apply equiv.subst_over_path_comp,
          transitivity, apply transport_there,
          transitivity, apply Id.map, apply ih,
          reflexivity } },
      { induction c with c ih,
        { apply transport_back },
        { transitivity, apply equiv.subst_over_path_comp,
          transitivity, apply transport_back,
          transitivity, apply Id.map, apply ih,
          reflexivity } }
    end)
    (begin
      apply theorems.funext,
      intro x, apply types.integer.set
    end) x c

  @[hott] noncomputable def family (x : S¹) : (base = x) ≃ helix x :=
  begin
    existsi encode x, split; existsi decode x,
    apply decode_encode x, apply encode_decode x
  end

  local notation ℤ := integer

  @[hott] noncomputable def fundamental_group : (Ω¹(S¹)) = ℤ :=
  ua (family base)

  @[hott] noncomputable def loop_hset : hset (base = base) :=
  transport hset fundamental_group⁻¹ (λ _ _, integer.set)

  @[hott] noncomputable def Ωind₁ {π : (Ω¹(S¹)) → Type u}
    (zeroπ : π Id.refl) (succπ : Π x, π x → π (x ⬝ loop))
    (predπ : Π x, π x → π (x ⬝ loop⁻¹)) : Π x, π x :=
  begin
    intro x, apply transport π, apply power_of_winding,
    fapply @types.integer.indsp (π ∘ power) _ _ _ (winding x),
    { exact zeroπ },
    { intros x ih, apply transport π,
      apply HITs.loop.power_comp circle.loop,
      apply succπ, exact ih },
    { intros x ih, apply transport π,
      apply HITs.loop.power_comp_pred,
      apply predπ, exact ih }
  end

  @[hott] noncomputable def Ωind₂ {π : (Ω¹(S¹)) → Type u}
    (zeroπ : π Id.refl) (succπ : Π x, π x → π (loop ⬝ x))
    (predπ : Π x, π x → π (loop⁻¹ ⬝ x)) : Π x, π x :=
  begin
    fapply Ωind₁, exact zeroπ, repeat { intros x ih, apply transport π, apply comm },
    apply succπ x ih, apply predπ x ih
  end

  @[hott] noncomputable example : winding (loop ⬝ loop) = integer.pos 2 :=
  encode_decode base (integer.pos 2)

  @[hott] noncomputable example : winding loop = integer.pos 1 :=
  encode_decode base (integer.pos 1)

  @[hott] noncomputable example : winding loop⁻¹ = integer.neg 0 :=
  encode_decode base (integer.neg 0)

  @[hott] def rot : Π (x : S¹), x = x :=
  circle.ind circle.loop (begin
    apply types.Id.trans, apply equiv.transport_inv_comp_comp,
    transitivity, apply Id.map (⬝ loop),
    apply Id.inv_comp, apply Id.refl_left
  end)

  def μₑ : S¹ → S¹ ≃ S¹ :=
  circle.rec (equiv.id S¹) (begin
    fapply sigma.prod,
    apply theorems.funext rot,
    apply theorems.prop.biinv_prop
  end)

  def μ (x : S¹) : S¹ → S¹ := (μₑ x).forward

  noncomputable def μ_loop : Id.map μ loop = theorems.funext rot :=
  begin
    transitivity, apply equiv.map_over_comp,
    transitivity, apply Id.map, apply recβrule₂,
    apply sigma.map_fst_over_prod
  end

  def inv : S¹ → S¹ :=
  circle.rec base loop⁻¹

  @[hott] noncomputable def inv_inv (x : S¹) : inv (inv x) = x :=
  let invₚ := @Id.map S¹ S¹ base base (inv ∘ inv) in
  begin
    fapply circle.ind _ _ x; clear x,
    { reflexivity },
    { calc
        equiv.transport (λ x, inv (inv x) = x) loop Id.refl =
                              invₚ loop⁻¹ ⬝ Id.refl ⬝ loop :
      by apply equiv.transport_over_involution
        ... = invₚ loop⁻¹ ⬝ (Id.refl ⬝ loop) :
      begin symmetry, apply Id.assoc end
        ... = inv # (inv # loop⁻¹) ⬝ loop :
      begin apply Id.map (⬝ loop), apply equiv.map_over_comp end
        ... = inv # (inv # loop)⁻¹ ⬝ loop :
      begin apply Id.map (⬝ loop),
            apply Id.map, apply Id.map_inv end
        ... = inv # loop⁻¹⁻¹ ⬝ loop :
      begin apply Id.map (⬝ loop),
            apply Id.map, apply Id.map,
            apply circle.recβrule₂ end
        ... = inv # loop ⬝ loop :
      begin apply Id.map (⬝ loop),
            apply Id.map, apply Id.inv_inv end
        ... = loop⁻¹ ⬝ loop :
      begin apply Id.map (⬝ loop), apply circle.recβrule₂ end
        ... = Id.refl : by apply Id.inv_comp }
  end

  @[hott] def unit_left (x : S¹) : μ base x = x :=
  by trivial

  @[hott] def μ_right : μ base # loop = loop :=
  by apply equiv.idmap

  @[hott] noncomputable def μ_left := calc
    (λ x, μ x base) # loop = happly (Id.map μ loop) base :
                             by apply interval.map_happly
                       ... = happly (theorems.funext rot) base :
                             begin apply Id.map (λ f, happly f base),
                                   apply μ_loop end
                       ... = loop :
                             begin change _ = rot base, apply happly,
                                   apply theorems.full.forward_right end

  @[hott] noncomputable def unit_right (x : S¹) : μ x base = x :=
  begin
    fapply circle.ind _ _ x, reflexivity, change _ = _,
    transitivity, apply equiv.transport_over_involution (λ x, μ x base),
    transitivity, apply Id.map (λ p, p ⬝ idp base ⬝ loop),
    transitivity, apply Id.map_inv, apply Id.map,
    apply μ_left, transitivity, apply Id.map (λ p, p ⬝ loop),
    apply Id.refl_right, apply Id.inv_comp
  end

  @[hott] noncomputable def unit_comm (x : S¹) : μ base x = μ x base :=
  (unit_right x)⁻¹

  @[hott] noncomputable def mul_inv (x : S¹) : base = μ x (inv x) :=
  begin
    fapply circle.ind _ _ x; clear x,
    { exact circle.loop },
    { apply Id.trans, apply equiv.transport_comp (λ x, base = x) (S μ inv) loop,
      transitivity, apply equiv.transport_composition,
      transitivity, apply Id.map, apply equiv.map_over_S,
      transitivity, apply Id.map, apply Id.map, apply circle.recβrule₂,
      transitivity, apply Id.map (⬝ equiv.bimap μ loop loop⁻¹),
      symmetry, apply μ_right,
      symmetry, transitivity, symmetry, apply μ_left,
      apply equiv.bimap_comp }
  end

  -- https://github.com/mortberg/cubicaltt/blob/master/examples/helix.ctt#L207
  @[hott] def lem_set_torus {π : S¹ → S¹ → Type u} (setπ : hset (π base base))
    (f : Π y, π base y) (g : Π x, π x base) (p : f base = g base) : Π x y, π x y :=
  begin
    intro x, fapply circle.ind _ _ x; clear x, exact f,
    change _ = _, transitivity, apply types.equiv.transport_over_pi,
    apply theorems.funext, intro y, fapply circle.ind _ _ y; clear y,
    change equiv.transport (λ (x : S¹), π x base) loop (f base) = _,
    transitivity, apply Id.map, exact p,
    transitivity, apply equiv.apd, exact p⁻¹, apply setπ
  end

  @[hott] noncomputable def groupoid : groupoid S¹ :=
  begin
    intros a b, change hset (a = b), fapply indΩ _ _ a; clear a,
    { fapply indΩ _ _ b; clear b, apply loop_hset,
      intro, apply structures.set_is_prop },
    intro, apply structures.set_is_prop
  end

  @[hott] noncomputable def mul_comm (x y : S¹) : μ x y = μ y x :=
  begin
    fapply @lem_set_torus (λ x y, μ x y = μ y x), apply loop_hset,
    { intro z, symmetry, apply unit_right },
    { intro z, apply unit_right }, reflexivity
  end

  @[hott] noncomputable def mul_assoc : Π x y z, μ x (μ y z) = μ (μ x y) z :=
  begin
    intro x, fapply @lem_set_torus (λ y z, μ x (μ y z) = μ (μ x y) z), apply groupoid,
    { intro z, apply Id.map (λ x, μ x z), exact (unit_right x)⁻¹ },
    { intro z, transitivity, apply Id.map, apply unit_right,
      symmetry, apply unit_right },
    { fapply ind _ _ x, reflexivity, apply groupoid }
  end

  @[hott] noncomputable def trans_comm {z : S¹} : Π (p q : z = z), p ⬝ q = q ⬝ p :=
  begin
    fapply ind _ _ z, { intros p q, apply comm },
    repeat { apply theorems.funext, intro }, apply groupoid
  end

  @[hott] noncomputable def transport_over_circle {z : S¹} {f g : S¹ → S¹} {p : f = g}
    (μ : f z = f z) (η : f z = g z) : @transport (S¹ → S¹) (λ φ, φ z = φ z) f g p μ = η⁻¹ ⬝ μ ⬝ η :=
  begin induction p, symmetry, apply id_conj_if_comm, apply trans_comm end

  open ground_zero.types.equiv (bimap)
  @[hott] noncomputable def mul_trans (p q : Ω¹(S¹)) : bimap μ p q = p ⬝ q :=
  begin
    transitivity, apply equiv.bimap_characterization, apply equiv.bimap,
    { transitivity, apply theorems.map_homotopy,
      intro x, symmetry, apply unit_right,
      transitivity, fapply transport_over_circle, reflexivity,
      transitivity, apply Id.refl_right, symmetry, apply idmap },
    { transitivity, apply theorems.map_homotopy,
      intro x, symmetry, apply unit_left,
      transitivity, fapply transport_over_circle, reflexivity,
      transitivity, apply Id.refl_right, symmetry, apply idmap }
  end

  def halfway.φ : I → S¹ :=
  λ i, interval.elim loop (i ∧ (interval.neg i))

  def halfway : base = base :=
  interval.lam halfway.φ

  @[hott] def halfway.const : halfway.φ ~ λ _, base :=
  begin
    fapply interval.ind,
    { reflexivity }, { reflexivity },
    { change _ = _, transitivity,
      apply types.equiv.transport_over_contr_map,
      transitivity, apply Id.refl_right,
      transitivity, apply Id.map_inv,
      transitivity, apply map, apply equiv.map_over_comp,
      transitivity, apply map, apply map, change _ = idp interval.zero,
      apply structures.prop_is_set, apply interval.interval_prop,
      reflexivity }
  end

  def pow' (x : S¹) : ℕ → S¹
  |    0    := base
  | (n + 1) := μ x (pow' n)

  def pow (x : S¹) : ℤ → S¹
  | (integer.pos n) := pow' x n
  | (integer.neg n) := pow' (inv x) (n + 1)
end circle

namespace ncircle
  def S : ℕ → Type
  |    0    := S⁰
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
  @[hott] def surf : idp base = idp base :=
  (types.Id.comp_inv loop)⁻¹ ⬝ surf_trans ⬝ (types.Id.comp_inv loop)

  @[hott] def rec {β : Type u} (b : β) (s : idp b = idp b) : S² → β :=
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

  @[hott] def Φ {π : Type u} {x x' y y' : π}
    (α : x = x') (β : y = y') :
    prod (idp x) β ⬝ prod α (idp y') =
    prod α (idp y) ⬝ prod (idp x') β :=
  begin induction α, induction β, trivial end

  @[hott] def t : p ⬝ q = q ⬝ p :> b = b :> T² :=
  Φ circle.loop circle.loop
end torus

inductive torus'.rel : I × I → I × I → Type
| top    (x : I) : torus'.rel ⟨0, x⟩ ⟨1, x⟩
| bottom (x : I) : torus'.rel ⟨x, 0⟩ ⟨x, 1⟩

def torus' : Type := graph torus'.rel

namespace torus'
  open interval

  def a : torus' := graph.elem ⟨1, 0⟩
  def b : torus' := graph.elem ⟨0, 0⟩
  def c : torus' := graph.elem ⟨0, 1⟩
  def d : torus' := graph.elem ⟨1, 1⟩

  @[hott] def top (x : I) : graph.elem ⟨0, x⟩ = graph.elem ⟨1, x⟩ :> torus' :=
  graph.line (rel.top x)

  @[hott] def bottom (x : I) : graph.elem ⟨x, 0⟩ = graph.elem ⟨x, 1⟩ :> torus' :=
  graph.line (rel.bottom x)

  @[hott] def p : b = b :> torus' :=
  graph.elem # (product.prod Id.refl seg) ⬝
  graph.elem # (product.prod seg     Id.refl) ⬝
  graph.elem # (product.prod Id.refl seg⁻¹) ⬝
  graph.elem # (product.prod seg⁻¹   Id.refl)

  @[hott] def q : b = b :> torus' :=
  bottom 0 ⬝ top 1 ⬝ (bottom 1)⁻¹ ⬝ (top 0)⁻¹
end torus'

end HITs

namespace types.integer
  local notation ℤ := integer
  noncomputable def succ_path := ground_zero.ua integer.succ_equiv

  noncomputable def shift : ℤ → ℤ = ℤ :=
  HITs.loop.power succ_path

  @[hott] noncomputable def shift_comp (z : ℤ) :
    shift z ⬝ succ_path = shift (integer.succ z) :=
  HITs.loop.power_comp succ_path z
end types.integer

end ground_zero