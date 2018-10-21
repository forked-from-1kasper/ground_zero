import ground_zero.unit ground_zero.equiv
import ground_zero.eq

open ground_zero.unit

namespace ground_zero

namespace structures
universe u

class prop (α : Sort u) :=
(intro : Π (a b : α), a = b :> α)

class hset (α : Type u) :=
(intro {a b : α} (p q : a = b :> α) : p = q :> _)

class contr (α : Sort u) :=
(point : α) (intro : Π (a : α), point = a :> α)

instance contr_is_prop (α : Sort u) [contr α] : prop α :=
⟨λ a b, (contr.intro a)⁻¹ ⬝ (contr.intro b)⟩

instance empty_is_prop : prop empty :=
⟨begin intros a, induction a end⟩

instance unit_is_prop : prop ground_zero.unit :=
⟨begin intros, induction a, induction b, trivial end⟩

instance prop_is_prop {α : Prop} : prop α :=
⟨begin intros, trivial end⟩

inductive Trunc (α : Sort u) : Prop
| elem : α → Trunc
def Trunc.uniq {α : Sort u} (a b : Trunc α) : a = b :> Trunc α :=
by trivial

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

instance signl_contr {α : Sort u} (a : α) : structures.contr (singl a) :=
{ point := trivial_loop a,
  intro := λ t, (path_from_trivial_loop t.intro) ⬝ (singl.eq t) }

end singl

end ground_zero