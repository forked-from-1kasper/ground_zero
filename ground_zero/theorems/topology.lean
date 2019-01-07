namespace ground_zero.theorems.topology
universe u

def subset {α : Sort u} (u v : α → Prop) :=
Π x, u x → v x

def disjoint {α : Sort u} (u v : α → Prop) :=
Π x, not (u x ∧ v x)

def union {α : Sort u} (β : (α → Prop) → Prop) :=
λ x, ∃ (u : α → Prop), β u ∧ u x

def inter {α : Sort u} (u v : α → Prop) :=
λ x, u x ∧ v x

def empty (α : Sort u) := λ (x : α), false
def full (α : Sort u) := λ (x : α), true

structure topology (α : Sort u) :=
(is_open : (α → Prop) → Prop)
(empty_open : is_open (empty α))
(full_open : is_open (full α))
(inter_open : Π u, is_open u → Π v, is_open v → is_open (inter u v))
(union_open : Π s, subset s is_open → is_open (union s))

end ground_zero.theorems.topology