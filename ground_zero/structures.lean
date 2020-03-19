import ground_zero.types.unit ground_zero.types.coproduct
open ground_zero.types.unit

hott theory

namespace ground_zero

namespace structures
universes u v

def is_loop {α : Type u} {a : α} (p : a = a) := ¬(p = types.eq.refl a)

def prop (α : Type u) :=
Π (a b : α), a = b :> α

def propset := Σ (α : Type u), prop α
notation `Ω` := propset

def hset (α : Type u) :=
Π {a b : α} (p q : a = b :> α), p = q :> a = b :> α

def dec (α : Type u) := α + ¬α

structure contr (α : Type u) :=
(point : α) (intro : Π (a : α), point = a :> α)
--  or we can write `idfun ~ λ _, point`

def {w} LEM := Π (α : Type w), prop α → (α + ¬α)
def law_of_double_negation :=
Π (α : Type u), prop α → (¬¬α → α)

def LEM_inf := Π (α : Type u), α + ¬α
notation `LEM∞` := LEM_inf

inductive homotopy_level
| minus_two
| succ : homotopy_level → homotopy_level

notation `−2` := homotopy_level.minus_two
notation `−1` := homotopy_level.succ −2

instance : has_zero homotopy_level := ⟨homotopy_level.succ −1⟩

def level_to_n : homotopy_level → ℕ
| homotopy_level.minus_two := 0
| (homotopy_level.succ n) := level_to_n n + 1

def n_to_level : ℕ → homotopy_level
| 0 := homotopy_level.minus_two
| (n + 1) := homotopy_level.succ (n_to_level n)

def is_n_type : Type u → homotopy_level → Type u
| α homotopy_level.minus_two := contr α
| α (homotopy_level.succ n) := Π (x y : α),
  is_n_type (x = y :> α) n

def n_type (n : homotopy_level) :=
Σ (α : Type u), is_n_type α n
notation n `-Type` := n_type n

def contr_impl_prop {α : Type u} (h : contr α) : prop α :=
λ a b, (h.intro a)⁻¹ ⬝ (h.intro b)

def empty_is_prop : prop 𝟎 :=
begin intros x, induction x end

def unit_is_prop : prop 𝟏 :=
begin intros x y, induction x, induction y, trivial end

def bool_to_universe : bool → Type
| tt := 𝟏
| ff := 𝟎

def ff_neq_tt : ¬(ff = tt) :=
λ h, ground_zero.types.equiv.transport bool_to_universe h⁻¹ ★

theorem function_space : ¬(Π {α β : Type}, prop (α → β)) :=
λ h, ff_neq_tt (types.equiv.homotopy.eq (h id bnot) ff)

theorem auto_contr {α : Type u} (x : α) (h : prop (α → α)) : prop α :=
begin
  apply contr_impl_prop, existsi x,
  apply types.equiv.homotopy.eq,
  apply h
end

section
  open types.equiv types.eq
  def prop_is_set {α : Type u} (r : prop α) : hset α := begin
    intros x y p q, have g := r x,
    transitivity, symmetry, apply rewrite_comp,
    exact (apd g p)⁻¹ ⬝ transport_composition p (g x),
    induction q, apply inv_comp
  end

  def empty_is_set : hset 𝟎 :=
  begin apply prop_is_set, apply empty_is_prop end
  def unit_is_set : hset 𝟏 :=
  begin apply prop_is_set, apply unit_is_prop end

  -- unsafe postulate, but it computes
  def function_extensionality {α : Type u} {β : α → Type v}
    {f g : Π x, β x} (h : f ~ g) : f = g :> Π x, β x :=
  support.inclusion $ funext (λ x, support.truncation (h x))

  def contr_is_prop {α : Type u} : prop (contr α) := begin
    intros x y, cases x with x u, cases y with y v,
    have p := u y, induction p, apply types.eq.map,
    apply function_extensionality, intro a,
    apply prop_is_set (contr_impl_prop ⟨x, u⟩)
  end

  def prop_is_prop {α : Type u} : prop (prop α) := begin
    intros f g,
    have p := λ a b, (prop_is_set f) (f a b) (g a b),
    apply function_extensionality, intro a,
    apply function_extensionality, intro b,
    exact p a b
  end

  def function_to_contr {α : Type u} : prop (α → contr α) := begin
    intros f g, apply function_extensionality, intro x, apply contr_is_prop
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

theorem K_iff_set (α : Type u) : K α ↔ hset α := begin
  split,
  { intro h, intros x y p q,
    induction q, apply h },
  { intro h, unfold K,
    intros, apply h }
end

def lem_prop {α : Type u} (h : α → prop α) : prop α :=
λ a, h a a

def lem_contr {α : Type u} (h : α → contr α) : prop α :=
λ a, contr_impl_prop (h a) a

def is_contr_fiber {α : Type u} {β : Type v} (f : α → β) :=
Π (y : β), contr (types.fib f y)

def prop_equiv_lemma {α : Type u} {β : Type v}
  (F : prop α) (G : prop β) (f : α → β) (g : β → α) : α ≃ β :=
begin
  existsi f, split; existsi g,
  { intro x, apply F }, { intro y, apply G }
end

end structures

-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/tiny-library.html
-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/hsetfunext.html
structure {u} singl {α : Type u} (a : α) :=
(point : α) (intro : a = point :> α)

namespace singl
universe u

def trivial_loop {α : Type u} (a : α) : singl a :=
⟨a, by reflexivity⟩

def path_from_trivial_loop {α : Type u} {a b : α}
  (r : a = b :> α) : (trivial_loop a) = ⟨b, r⟩ :> singl a :=
begin induction r, trivial end

def singl.eq {α : Type u} {a : α} (t : singl a) :
  { point := t.point, intro := t.intro } = t :> singl a :=
begin induction t, simp end

def signl_contr {α : Type u} (a : α) : structures.contr (singl a) :=
{ point := trivial_loop a,
  intro := λ t, path_from_trivial_loop t.intro ⬝ singl.eq t }

def singl_prop {α : Type u} (a : α) : structures.prop (singl a) :=
structures.contr_impl_prop (signl_contr a)

end singl

end ground_zero