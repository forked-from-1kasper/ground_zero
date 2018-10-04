namespace ground_zero.structures

universe u

class prop (α : Sort u) :=
(intro : Π (a b : α), a = b)

class hset (α : Type u) :=
(intro {a b : α} : prop (a = b))

class contr (α : Sort u) :=
(point : α) (intro : Π (a : α), point = a)

instance contr_is_prop (α : Sort u) [contr α] : prop α :=
⟨λ a b, eq.trans (eq.symm $ contr.intro a) (contr.intro b)⟩

end ground_zero.structures