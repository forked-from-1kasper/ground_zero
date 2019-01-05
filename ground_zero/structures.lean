import ground_zero.types.unit ground_zero.types.coproduct
open ground_zero.types.unit

namespace ground_zero

namespace structures
universes u v

def prop (α : Sort u) :=
Π (a b : α), a = b :> α

def hset (α : Sort u) :=
Π {a b : α} (p q : a = b :> α), p = q :> a = b :> α

structure contr (α : Sort u) :=
(point : α) (intro : Π (a : α), point = a :> α)

def LEM := Π (α : Type u), prop α → (α + ¬α)
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

def is_n_type : Sort u → homotopy_level → Sort (max 1 u)
| α homotopy_level.minus_two := contr α
| α (homotopy_level.succ n) := Π (x y : α),
  is_n_type (x = y :> α) n

def n_type (n : homotopy_level) :=
Σ' (α : Sort u), is_n_type α n
notation n `-Type` := n_type n

def contr_is_prop {α : Sort u} (h : contr α) : prop α :=
λ a b, (h.intro a)⁻¹ ⬝ (h.intro b)

def empty_is_prop : prop empty :=
begin intros x, induction x end

def unit_is_prop : prop types.unit :=
begin intros x y, induction x, induction y, trivial end

def prop_is_prop {α : Prop} : prop α :=
begin intros x y, trivial end

inductive truncation (α : Sort u) : Prop
| elem : α → truncation
def truncation.uniq {α : Sort u} (a b : truncation α) :
  a = b :> truncation α := types.eq.rfl

def K (α : Sort u) :=
Π (a : α) (p : a = a :> α), p = types.eq.refl a :> a = a :> α

theorem K_iff_set (α : Sort u) : K α ↔ hset α := begin
  split,
  { intro h, intros x y p q,
    induction q, apply h },
  { intro h, unfold K,
    intros, apply h }
end

def lem_prop {α : Sort u} (h : α → prop α) : prop α :=
λ a, h a a

def is_contr_fiber {α : Sort u} {β : Sort v} (f : α → β) :=
Π (y : β), contr (types.fib f y)

end structures

-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/tiny-library.html
-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/hsetfunext.html
structure {u} singl {α : Sort u} (a : α) :=
(point : α) (intro : a = point :> α)

namespace singl
universe u

def trivial_loop {α : Sort u} (a : α) : singl a :=
⟨a, by reflexivity⟩

def path_from_trivial_loop {α : Sort u} {a b : α}
  (r : a = b :> α) : (trivial_loop a) = ⟨b, r⟩ :> singl a :=
begin induction r, trivial end

def singl.eq {α : Sort u} {a : α} (t : singl a) :
  { point := t.point, intro := t.intro } = t :> singl a :=
begin induction t, simp end

def signl_contr {α : Sort u} (a : α) : structures.contr (singl a) :=
{ point := trivial_loop a,
  intro := λ t, path_from_trivial_loop t.intro ⬝ singl.eq t }

end singl

end ground_zero