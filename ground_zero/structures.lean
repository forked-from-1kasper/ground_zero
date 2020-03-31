import ground_zero.types.unit ground_zero.types.coproduct
import ground_zero.theorems.funext
open ground_zero.types.unit

hott theory

namespace ground_zero

namespace structures
universes u v w

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

inductive level
| minus_two
| succ : level → level

notation `ℕ₋₂` := level
notation `−2` := level.minus_two
notation `−1` := level.succ −2

instance : has_zero level := ⟨level.succ −1⟩
instance : has_one  level := ⟨level.succ 0⟩

namespace level
  inductive le : level → level → Type
  | refl (a : level)   : le a a
  | step (a b : level) : le a b → le a (succ b)
  infix ` ≤ ` := le

  def le.minus_two (a : level) : −2 ≤ a := begin
    induction a with a ih,
    { apply le.refl },
    { apply le.step, assumption }
  end

  def le.succ (a b : level) : a ≤ b → succ a ≤ succ b := begin
    intro h, induction h with c a' b' h ih,
    { apply le.refl },
    { apply le.step, assumption }
  end

  def add : level → level → level
  | (succ (succ n)) −2 := n
  | −1 −2 := −2
  | −2 −2 := −2
  | n 0 := n
  | n (succ m) := succ (add n m)
  instance : has_add level := ⟨level.add⟩

  def of_nat : ℕ → ℕ₋₂
  |    0    := 0
  | (n + 1) := level.succ (of_nat n)
end level

def is_n_type : level → Type u → Type u
| level.minus_two := contr
| (level.succ n)  := λ α, Π (x y : α), is_n_type n (x = y)
notation [parsing_only] `is-` n `-type ` α := is_n_type n α

def n_type (n : level) :=
Σ (α : Type u), is_n_type n α
notation n `-Type` := n_type n

@[hott] def level.cumulative (n : level) : Π {α : Type u},
  (is-n-type α) → is-(level.succ n)-type α := begin
  induction n with n ih; intros α h,
  { induction h with a₀ p,
    intros x y, existsi (p x)⁻¹ ⬝ p y,
    intro q, induction q, apply types.eq.inv_comp },
  { intros x y, apply ih, apply h }
end

@[hott] def level.strong_cumulative (n m : level) (h : n ≤ m) :
  Π {α : Type u}, (is-n-type α) → (is-m-type α) := begin
  induction h with c a' b' h ih,
  { intros, assumption },
  { intros α g, apply level.cumulative,
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
    apply theorems.dfunext, intro a,
    apply prop_is_set (contr_impl_prop ⟨x, u⟩)
  end

  @[hott] def prop_is_prop {α : Type u} : prop (prop α) := begin
    intros f g, repeat { apply theorems.dfunext, intro },
    apply prop_is_set, assumption
  end

  @[hott] def set_is_prop {α : Type u} : prop (hset α) := begin
    intros f g, repeat { apply theorems.dfunext, intro },
    apply set_impl_groupoid, assumption
  end

  @[hott] def ntype_is_prop (n : level) : Π {α : Type u}, prop (is-n-type α) := begin
    induction n with n ih,
    { apply contr_is_prop },
    { intros α p q, apply theorems.dfunext,
      intro x, apply theorems.dfunext, intro y,
      apply ih }
  end

  @[hott] def function_to_contr {α : Type u} : prop (α → contr α) := begin
    intros f g, apply theorems.funext, intro x, apply contr_is_prop
  end
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
    intro f, apply theorems.dfunext,
    intro x, apply (h x).left_forward },
  { existsi (λ (f : Π x, μ x) (x : α), (h x).right (f x)),
    intro f, apply theorems.dfunext,
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

end structures

-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/tiny-library.html
-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/hsetfunext.html
structure {u} singl {α : Type u} (a : α) :=
(point : α) (intro : a = point :> α)

namespace singl
universe u

def trivial_loop {α : Type u} (a : α) : singl a :=
⟨a, by reflexivity⟩

@[hott] def path_from_trivial_loop {α : Type u} {a b : α}
  (r : a = b :> α) : (trivial_loop a) = ⟨b, r⟩ :> singl a :=
begin induction r, trivial end

@[hott] def singl.eq {α : Type u} {a : α} (t : singl a) :
  { point := t.point, intro := t.intro } = t :> singl a :=
begin induction t, trivial end

@[hott] def signl_contr {α : Type u} (a : α) : structures.contr (singl a) :=
{ point := trivial_loop a,
  intro := λ t, path_from_trivial_loop t.intro ⬝ singl.eq t }

@[hott] def singl_prop {α : Type u} (a : α) : structures.prop (singl a) :=
structures.contr_impl_prop (signl_contr a)

end singl

end ground_zero