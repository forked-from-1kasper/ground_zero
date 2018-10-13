namespace ground_zero.heq

universes u v
def from_homo {α : Type u} {a b : α} (h : a = b) : a == b :=
begin induction h, reflexivity end

def map {α : Sort u} {β : α → Sort v} {a b : α}
(f : Π (x : α), β x) (p : a = b) : f a == f b :=
begin induction p, reflexivity end

def only_refl {α : Type u} {a b : α} (p : a = b) : p == (eq.refl a) :=
begin induction p, trivial end

end ground_zero.heq