import ground_zero.types.equiv

namespace ground_zero.types.heq

universes u v
def from_homo {α : Sort u} {a b : α} (h : a = b) : a == b :=
begin induction h, reflexivity end

def inclusion {α : Sort u} {a b : α} : (a = b :> α) → a == b :=
from_homo ∘ ground_zero.support.truncation

def map {α : Sort u} {β : α → Sort v} {a b : α}
(f : Π (x : α), β x) (p : a = b) : f a == f b :=
begin induction p, reflexivity end

def only_refl {α : Sort u} {a b : α} (p : a = b) : p == (eq.refl a) :=
begin induction p, trivial end

lemma eq_subst_heq {α : Sort u} {π : α → Sort v}
  {a b : α} (p : a = b :> α) (x : π a) :
  x == ground_zero.types.equiv.subst p x :=
begin induction p, reflexivity end

def from_pathover {α : Sort u} {π : α → Sort v}
  {a b : α} (p : a = b :> α) {u : π a} {v : π b}
  (q : u =[p] v) : u == v :=
begin induction q, apply eq_subst_heq end

end ground_zero.types.heq