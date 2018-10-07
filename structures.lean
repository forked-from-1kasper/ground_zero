import ground_zero.unit
open ground_zero.unit

namespace ground_zero.structures

universe u

class prop (α : Sort u) :=
(intro : Π (a b : α), a = b)

class hset (α : Type u) :=
(intro {a b : α} (p q : a = b) : p = q)

class contr (α : Sort u) :=
(point : α) (intro : Π (a : α), point = a)

instance contr_is_prop (α : Sort u) [contr α] : prop α :=
⟨λ a b, eq.trans (eq.symm $ contr.intro a) (contr.intro b)⟩

instance empty_is_prop : prop empty :=
⟨begin intros a, induction a end⟩

instance unit_is_prop : prop ground_zero.unit :=
⟨begin intros, induction a, induction b, trivial end⟩

end ground_zero.structures