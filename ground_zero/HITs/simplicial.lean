import ground_zero.HITs.merely
open ground_zero.types.eq (renaming rfl -> idp)
open ground_zero.structures (prop)
open ground_zero (iter vect vect.map vect.constant)
open ground_zero.types

hott theory

namespace ground_zero.HITs
universes u v w

def neq {α : Type u} (a b : α) : Type u := a = b → (𝟎 : Type)

def fin := iter 𝟏 𝟏
def filled (n : ℕ) := ∥fin n∥

def network (α : Type u) := graph (@neq α)

def network.decode {α : Type u} (H : prop α) : network α → α := begin
  fapply graph.ind,
  { exact id },
  { intros x y G, apply ground_zero.proto.empty.elim,
    apply G, apply H }
end

def network.prop {α : Type u} (H : prop α) : prop (network α) := begin
  intros x y, fapply graph.ind _ _ x; clear x; intro x,
  { fapply graph.ind _ _ y; clear y; intro y,
    { apply eq.map, apply H },
    { intros z G, apply ground_zero.proto.empty.elim,
      apply G, apply H } },
  { intros z G, apply ground_zero.proto.empty.elim,
    apply G, apply H }
end

def network.proplem {α : Type u} (H : prop α) : α ≃ network α := begin
  apply ground_zero.structures.prop_equiv_lemma,
  apply H, apply network.prop H,
  apply graph.elem, apply network.decode H
end

def hull (n : ℕ) := network (fin n)
def hull.elem {n : ℕ} : fin n → hull n := graph.elem

inductive tetrahedron (n : ℕ) (α : Type u) : vect α n → Type u
| refl {} (a : α) : tetrahedron (vect.constant a n)

def tetrahedron.map {n : ℕ} {α : Type u} {β : Type v} (f : α → β)
  (x : vect α n) (p : tetrahedron n α x) : tetrahedron n β (vect.map f x) := begin
  induction p, apply ground_zero.types.equiv.transport,
  { symmetry, apply ground_zero.vect.const_map },
  apply tetrahedron.refl
end

end ground_zero.HITs