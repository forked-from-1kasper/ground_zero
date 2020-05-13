import ground_zero.types.unit ground_zero.types.coproduct
import ground_zero.types.product ground_zero.types.sigma
open ground_zero.types.unit ground_zero.types.eq (map)
open ground_zero.types (coproduct)

hott theory

namespace ground_zero
universes u v w

namespace structures
def is_loop {α : Type u} {a : α} (p : a = a) := ¬(p = types.eq.refl a)

def prop (α : Type u) :=
Π (a b : α), a = b :> α

def propset := Σ (α : Type u), prop α
notation `Ω` := propset

def hset (α : Type u) :=
Π {a b : α} (p q : a = b), p = q
def Ens := Σ α, hset α

def groupoid (α : Type u) :=
Π {a b : α} {p q : a = b} (α β : p = q), α = β

def dec (α : Type u) := α + ¬α

structure contr (α : Type u) :=
(point : α) (intro : Π (a : α), point = a :> α)
--  or we can write `idfun ~ λ _, point`

def LEM := Π (α : Type w), prop α → (α + ¬α)
def law_of_double_negation :=
Π (α : Type u), prop α → (¬¬α → α)

def LEM_inf := Π (α : Type u), α + ¬α
notation `LEM∞` := LEM_inf

inductive hlevel
| minus_two
| succ : hlevel → hlevel

notation `ℕ₋₂` := hlevel
notation `−2` := hlevel.minus_two
notation `−1` := hlevel.succ −2

instance : has_zero hlevel := ⟨hlevel.succ −1⟩
instance : has_one  hlevel := ⟨hlevel.succ 0⟩

namespace hlevel
  inductive le : hlevel → hlevel → Type
  | refl (a : hlevel)   : le a a
  | step (a b : hlevel) : le a b → le a (succ b)
  infix ` ≤ ` := le

  def le.minus_two (a : hlevel) : −2 ≤ a := begin
    induction a with a ih,
    { apply le.refl },
    { apply le.step, assumption }
  end

  def le.succ (a b : hlevel) : a ≤ b → succ a ≤ succ b := begin
    intro h, induction h with c a' b' h ih,
    { apply le.refl },
    { apply le.step, assumption }
  end

  def add : hlevel → hlevel → hlevel
  | (succ (succ n)) −2 := n
  | −1 −2 := −2
  | −2 −2 := −2
  | n 0 := n
  | n (succ m) := succ (add n m)
  instance : has_add hlevel := ⟨hlevel.add⟩

  def of_nat : ℕ → ℕ₋₂
  |    0    := 0
  | (n + 1) := hlevel.succ (of_nat n)
end hlevel

def is_n_type : hlevel → Type u → Type u
| hlevel.minus_two := contr
| (hlevel.succ n)  := λ α, Π (x y : α), is_n_type n (x = y)
notation [parsing_only] `is-` n `-type ` := is_n_type n

def n_type (n : hlevel) :=
Σ (α : Type u), is_n_type n α
notation n `-Type` := n_type n

@[hott] def hlevel.cumulative (n : hlevel) : Π {α : Type u},
  (is-n-type α) → is-(hlevel.succ n)-type α := begin
  induction n with n ih; intros α h,
  { induction h with a₀ p,
    intros x y, existsi (p x)⁻¹ ⬝ p y,
    intro q, induction q, apply types.eq.inv_comp },
  { intros x y, apply ih, apply h }
end

@[hott] def hlevel.strong_cumulative (n m : hlevel) (h : n ≤ m) :
  Π {α : Type u}, (is-n-type α) → (is-m-type α) := begin
  induction h with c a' b' h ih,
  { intros, assumption },
  { intros α g, apply hlevel.cumulative,
    apply ih, assumption }
end

@[hott] def contr_impl_prop {α : Type u} (h : contr α) : prop α :=
λ a b, (h.intro a)⁻¹ ⬝ (h.intro b)

def empty_is_prop : prop 𝟎 :=
begin intros x, induction x end

def unit_is_prop : prop 𝟏 :=
begin intros x y, induction x, induction y, trivial end

@[hott] def contr_equiv_unit {α : Type u} (h : contr α) : α ≃ 𝟏 := begin
  existsi (λ _, ★), split;
  existsi (λ _, h.point),
  { intro x, apply h.intro },
  { intro x, cases x, reflexivity }
end

@[hott] def prod_unit_equiv (α : Type u) : 𝟏 × α ≃ α := begin
  existsi prod.snd, split;
  existsi prod.mk ★,
  { intro x, induction x with a b,
    induction a, trivial },
  { intro x, trivial }
end

def bool_to_universe : bool → Type
| tt := 𝟏
| ff := 𝟎

@[hott] def ff_neq_tt : ¬(ff = tt) :=
λ h, ground_zero.types.equiv.transport bool_to_universe h⁻¹ ★

@[hott] theorem function_space : ¬(Π {α β : Type}, prop (α → β)) :=
λ h, ff_neq_tt (types.equiv.homotopy.eq (h id bnot) ff)

@[hott] theorem auto_contr {α : Type u} (x : α)
  (h : prop (α → α)) : prop α := begin
  apply contr_impl_prop, existsi x,
  apply types.equiv.homotopy.eq,
  apply h
end

section
  open types.equiv types.eq
  @[hott] def prop_is_set {α : Type u} (r : prop α) : hset α := begin
    intros x y p q, have g := r x,
    transitivity, symmetry, apply rewrite_comp,
    exact (apd g p)⁻¹ ⬝ transport_composition p (g x),
    induction q, apply inv_comp
  end

  @[hott] def set_impl_groupoid {α : Type u} (r : hset α) : groupoid α := begin
    intros a b p q η μ, have g := r p,
    transitivity, symmetry, apply rewrite_comp,
    transitivity, symmetry, exact apd g η, apply transport_composition,
    induction μ, apply inv_comp
  end

  @[hott] def empty_is_set : hset 𝟎 :=
  begin apply prop_is_set, apply empty_is_prop end
  @[hott] def unit_is_set : hset 𝟏 :=
  begin apply prop_is_set, apply unit_is_prop end

  @[hott] def contr_is_prop {α : Type u} : prop (contr α) := begin
    intros x y, cases x with x u, cases y with y v,
    have p := u y, induction p, apply types.eq.map,
    apply HITs.interval.funext, intro a,
    apply prop_is_set (contr_impl_prop ⟨x, u⟩)
  end

  @[hott] def prop_is_prop {α : Type u} : prop (prop α) := begin
    intros f g, repeat { apply HITs.interval.funext, intro },
    apply prop_is_set, assumption
  end

  @[hott] def set_is_prop {α : Type u} : prop (hset α) := begin
    intros f g, repeat { apply HITs.interval.funext, intro },
    apply set_impl_groupoid, assumption
  end

  @[hott] def ntype_is_prop (n : hlevel) : Π {α : Type u}, prop (is-n-type α) := begin
    induction n with n ih,
    { apply contr_is_prop },
    { intros α p q, apply HITs.interval.funext,
      intro x, apply HITs.interval.funext, intro y,
      apply ih }
  end

  @[hott] def function_to_contr {α : Type u} : prop (α → contr α) := begin
    intros f g, apply HITs.interval.funext, intro x, apply contr_is_prop
  end
end

@[hott] def retract (β : Type u) (α : Type v) :=
Σ (r : α → β) (s : β → α), r ∘ s ~ id

@[hott] def retract.section {β : Type u} {α : Type v} : retract β α → β → α
| ⟨_, s, _⟩ := s

@[hott] def contr_retract {α : Type u} {β : Type v} :
  retract β α → contr α → contr β
| ⟨r, s, ε⟩ ⟨a₀, p⟩ :=
⟨r a₀, λ b, r # (p (s b)) ⬝ (ε b)⟩

@[hott] def retract.path {α : Type u} {β : Type v} :
  Π (H : retract β α) {a b : β},
  retract (a = b) (H.section a = H.section b)
| ⟨r, s, ε⟩ a b := ⟨λ q, (ε a)⁻¹ ⬝ (@map α β _ _ r q) ⬝ (ε b), map s,
begin
  intro p, transitivity, symmetry, apply types.eq.assoc,
  symmetry, apply types.equiv.inv_rewrite_comp,
  transitivity, calc
    (ε a)⁻¹⁻¹ ⬝ p = ε a ⬝ p               : (⬝ p) # (types.eq.inv_inv (ε a))
              ... = ε a ⬝ proto.idfun # p : (λ p, ε a ⬝ p) # (types.equiv.idmap p)⁻¹,
  symmetry, transitivity,
  { apply map (⬝ ε b),
    apply (types.equiv.map_over_comp s r p)⁻¹ },
  apply (types.equiv.homotopy_square ε p)⁻¹
end⟩

@[hott] def equiv_respects_rectraction {n : ℕ₋₂} :
  Π {α : Type u} {β : Type v},
    retract β α → is-n-type α → is-n-type β := begin
  induction n with n ih,
  { apply ground_zero.structures.contr_retract },
  { intros α β G H, intros a b,
    fapply ih, apply retract.path G,
    apply H }
end

@[hott] def equiv_induces_retraction {α β : Type u} : α ≃ β → retract β α
| ⟨f, (_, ⟨g, ε⟩)⟩ := ⟨f, g, ε⟩

@[hott] def ntype_respects_equiv (n : ℕ₋₂) {α β : Type u} :
  α ≃ β → is-n-type α → is-n-type β :=
equiv_respects_rectraction ∘ equiv_induces_retraction

@[hott] def ntype_respects_sigma (n : ℕ₋₂) :
  Π {α : Type u} {β : α → Type v},
    is-n-type α → (Π x, is-n-type (β x)) → is-n-type (Σ x, β x) := begin
  induction n with n ih,
  { intros α β A B, induction A with a₀ p,
    existsi sigma.mk a₀ (B a₀).point,
    intro x, induction x with a b,
    fapply types.sigma.prod,
    { apply p },
    { apply contr_impl_prop, apply B } },
  { intros α β A B, intros p q,
    apply ntype_respects_equiv,
    symmetry, apply types.sigma.sigma_path,
    apply ih, apply A, { intro x, apply B } }
end

inductive squash' (α : Type u) : Prop
| elem : α → squash'

inductive lift (α : Prop) : Type
| elem : α → lift

def squash := lift ∘ squash'

def squash.elem {α : Type u} : α → squash α :=
lift.elem ∘ squash'.elem

def squash.uniq {α : Type u} (a b : squash α) : a = b :=
begin induction a, induction b, trivial end

def squash.prop {α : Type u} {β : Prop}
  (f : α → β) : squash α → β :=
begin intro h, repeat { induction h }, apply f h end

def squash.lift {α : Type u} {β : Type v}
  (f : α → β) : squash α → squash β :=
lift.elem ∘ squash.prop (squash'.elem ∘ f)

def K (α : Type u) :=
Π (a : α) (p : a = a :> α), p = types.eq.refl a :> a = a :> α

@[hott] theorem K_iff_set (α : Type u) : K α ↔ hset α := begin
  split,
  { intro h, intros x y p q,
    induction q, apply h },
  { intros h a p, apply h }
end

@[hott] def lem_prop {α : Type u} (h : α → prop α) : prop α :=
λ a, h a a

@[hott] def lem_contr {α : Type u} (h : α → contr α) : prop α :=
λ a, contr_impl_prop (h a) a

def is_contr_fiber {α : Type u} {β : Type v} (f : α → β) :=
Π (y : β), contr (types.fib f y)

@[hott] def prop_equiv_lemma {α : Type u} {β : Type v}
  (F : prop α) (G : prop β) (f : α → β) (g : β → α) : α ≃ β :=
begin
  existsi f, split; existsi g,
  { intro x, apply F }, { intro y, apply G }
end

@[hott] def minus_two_eqv_contr {α : Type u} : (is-(−2)-type α) ≃ contr α :=
by refl

@[hott] def minus_one_eqv_prop {α : Type u} : (is-(−1)-type α) ≃ prop α := begin
  apply prop_equiv_lemma, apply ntype_is_prop, apply prop_is_prop,
  { intros h a b, exact (h a b).point },
  { intros h a b, existsi h a b, apply prop_is_set h }
end

@[hott] def equiv_funext {α : Type u} {η μ : α → Type v}
  (h : Π x, η x ≃ μ x) : (Π x, η x) ≃ (Π x, μ x) := begin
  existsi (λ (f : Π x, η x) (x : α), (h x).forward (f x)), split,
  { existsi (λ (f : Π x, μ x) (x : α), (h x).left (f x)),
    intro f, apply HITs.interval.funext,
    intro x, apply (h x).left_forward },
  { existsi (λ (f : Π x, μ x) (x : α), (h x).right (f x)),
    intro f, apply HITs.interval.funext,
    intro x, apply (h x).forward_right }
end

@[hott] def zero_eqv_set {α : Type u} : (is-0-type α) ≃ hset α := calc
  (is-0-type α) ≃ (Π x y, is-(−1)-type (x = y)) : by reflexivity
            ... ≃ (Π (x y : α), prop (x = y)) :
                  begin apply equiv_funext, intro x,
                        apply equiv_funext, intro y,
                        apply minus_one_eqv_prop end
            ... ≃ hset α : by reflexivity

@[hott] def one_eqv_groupoid {α : Type u} : (is-1-type α) ≃ groupoid α := calc
  (is-1-type α) ≃ (Π x y, is-0-type (x = y)) : by reflexivity
            ... ≃ (Π (x y : α), hset (x = y)) :
                   begin apply equiv_funext, intro x,
                         apply equiv_funext, intro y,
                         apply zero_eqv_set end
            ... ≃ groupoid α : by reflexivity

@[hott] def hset_respects_equiv {α β : Type u} :
  α ≃ β → hset α → hset β := begin
  intros e h, apply zero_eqv_set.forward,
  apply ntype_respects_equiv 0 e,
  apply zero_eqv_set.left, assumption
end

@[hott] def contr_respects_equiv {α β : Type u} :
  α ≃ β → contr α → contr β :=
by apply ntype_respects_equiv −2

@[hott] def product_prop {α : Type u} {β : Type v}
  (h : prop α) (g : prop β) : prop (α × β) := begin
  intros a b,
  cases a with x y, cases b with u v,
  have p := h x u, have q := g y v,
  induction p, induction q, reflexivity
end

@[hott] def pi_prop {α : Type u} {β : α → Type v}
  (h : Π x, prop (β x)) : prop (Π x, β x) :=
λ f g, HITs.interval.funext (λ x, h x (f x) (g x))

@[hott] def impl_prop {α : Type u} {β : Type v}
  (h : prop β) : prop (α → β) :=
pi_prop (λ _, h)

@[hott] def refl_mere_rel {α : Type u} (R : α → α → Type v) (h : Π x y, prop (R x y))
  (ρ : Π x, R x x) (f : Π x y, R x y → x = y) : hset α := begin
  intros a b p q, induction q, symmetry,
  apply types.eq.trans_cancel_left (f a a (ρ a)),
  transitivity, { apply types.eq.refl_right }, symmetry,
  transitivity, { symmetry, apply types.equiv.transport_composition },
  transitivity, { apply types.equiv.lifted_happly (R a),
                  apply types.equiv.apd (f a) p },
  apply types.eq.map, apply h
end

@[hott] def double_neg_eq {α : Type u} (h : Π (x y : α), ¬¬(x = y) → x = y) : hset α := begin
  fapply refl_mere_rel,
  { intros x y, exact ¬¬(x = y) },
  { intros x y, apply impl_prop, apply empty_is_prop },
  { intro x, intros f, apply f, reflexivity },
  { exact h }
end

@[hott] def lem_to_double_neg {α : Type u} : dec α → (¬¬α → α)
| (sum.inl x) := λ _, x
| (sum.inr t) := λ g, proto.empty.rec (λ _, α) (g t)

@[hott] def Hedberg {α : Type u} : (Π (x y : α), dec (x = y)) → hset α := begin
  intro h, apply double_neg_eq,
  intros x y, apply lem_to_double_neg, apply h x y
end

end structures

-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/tiny-library.html
-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/hsetfunext.html
def singl {α : Type u} (a : α) :=
Σ b, a = b

namespace singl
  def trivial_loop {α : Type u} (a : α) : singl a :=
  ⟨a, by reflexivity⟩

  @[hott] def path_from_trivial_loop {α : Type u} {a b : α}
    (r : a = b) : (trivial_loop a) = ⟨b, r⟩ :> singl a :=
  begin induction r, trivial end

  @[hott] def singl.eta {α : Type u} {a : α} (t : singl a) :
    ⟨t.fst, t.snd⟩ = t :> singl a :=
  begin induction t, trivial end

  @[hott] def contr {α : Type u} (a : α) : structures.contr (singl a) :=
  ⟨trivial_loop a, λ t, path_from_trivial_loop t.snd ⬝ singl.eta t⟩

  @[hott] def prop {α : Type u} (a : α) : structures.prop (singl a) :=
  structures.contr_impl_prop (contr a)
end singl

namespace theorems
  open ground_zero.structures ground_zero.types.equiv ground_zero.types

  @[hott] def naive {α : Type u} {β : α → Type v} {f g : Π x, β x} : f ~ g → f = g :=
  HITs.interval.funext

  @[hott] def weak {α : Type u} {β : α → Type v}
    (H : Π x, contr (β x)) : contr (Π x, β x) := begin
    existsi (λ x, (H x).point),
    intro f, apply naive, intro x, apply (H x).intro
  end

  section
    variables {α : Type u} {β : α → Type v}

    @[hott] def is_contr_sigma_homotopy
      (f : Π x, β x) : contr (Σ g, f ~ g) :=
    let r (k : Π x, Σ y, f x = y) :=
    @sigma.mk _ (λ g, f ~ g) (λ x, (k x).fst) (λ x, (k x).snd) in
    let s (g : Π x, β x) (h : f ~ g) x :=
    sigma.mk (g x) (h x) in begin
      existsi sigma.mk f (homotopy.id f),
      intro g, induction g with g H,
      change r (λ x, sigma.mk (f x) (idp _)) = r (s g H),
      apply eq.map r, apply contr_impl_prop,
      apply weak, intro x, apply singl.contr
    end

    variables (f : Π x, β x) {π : Π g (h : f ~ g), Type w}
              (r : π f (homotopy.id f))
    @[hott] def homotopy_ind 
      (g : Π x, β x) (h : f ~ g) : π g h :=
    @transport (Σ g, f ~ g) (λ (p : Σ g, f ~ g), π p.fst p.snd)
      ⟨f, homotopy.id f⟩ ⟨g, h⟩
      (contr_impl_prop (is_contr_sigma_homotopy f) _ _) r

    @[hott] def homotopy_ind_id :
      homotopy_ind f r f (types.equiv.homotopy.id f) = r := begin
      transitivity, apply eq.map
        (λ p, @transport (Σ g, f ~ g) (λ p, π p.fst p.snd)
           ⟨f, equiv.homotopy.id f⟩ ⟨f, equiv.homotopy.id f⟩ p r),
      change _ = idp _,
      apply prop_is_set, apply contr_impl_prop,
      apply is_contr_sigma_homotopy,
      trivial
    end
  end

  @[hott] def funext {α : Type u} {β : α → Type v}
    {f g : Π x, β x} : (f ~ g) → (f = g) :=
  @homotopy_ind _ _ f (λ g x, f = g) (idp _) g

  @[hott] def full {α : Type u} {β : α → Type v}
    {f g : Π x, β x} : (f = g) ≃ (f ~ g) := begin
    existsi HITs.interval.happly, split; existsi funext,
    { intro x, induction x, apply homotopy_ind_id },
    { apply homotopy_ind, change _ = HITs.interval.happly (idp _),
      apply eq.map HITs.interval.happly, apply homotopy_ind_id }
  end
end theorems

@[hott] def structures.pi_respects_ntype (n : ℕ₋₂) :
  Π {α : Type u} {β : α → Type v}
    (H : Π x, is-n-type (β x)), is-n-type (Π x, β x) := begin
  induction n with n ih,
  { intros, existsi (λ x, (H x).point),
    intro h, apply ground_zero.theorems.funext, intro x,
    apply (H x).intro },
  { intros, intros f g, apply structures.ntype_respects_equiv,
    symmetry, apply ground_zero.theorems.full,
    apply ih, intro x, apply H }
end

def iter (α β : Type) : ℕ → Type
|    0    := β
| (n + 1) := coproduct (iter n) α
def pt := iter 𝟏

def vect (α : Type u) : ℕ → Type u
|    0    := 𝟏
| (n + 1) := vect n × α

def vect.constant {α : Type u} (a : α) : Π n, vect α n
|    0    := ★
| (n + 1) := (vect.constant n, a)

def vect.map {α : Type u} {β : Type v} (f : α → β) :
  Π {n : ℕ}, vect α n → vect β n 
|    0    := λ _, ★
| (n + 1) := λ v, (vect.map v.1, f v.2)

@[hott] def vect.const_map {α : Type u} {β : Type v} (a : α) (f : α → β) :
  Π {n : ℕ}, vect.map f (vect.constant a n) = vect.constant (f a) n := begin
  intro n, induction n with n ih,
  { reflexivity },
  { fapply ground_zero.types.product.prod,
    { apply ih },
    { reflexivity } }
end

end ground_zero