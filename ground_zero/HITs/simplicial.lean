import ground_zero.HITs.merely ground_zero.types.integer
open ground_zero (iter vect vect.map vect.constant)
open ground_zero.structures (prop)
open ground_zero.types
open ground_zero

local notation `ℤ` := ground_zero.types.integer

hott theory

namespace ground_zero.HITs
universes u v w

def simplex (α : Type u) (n : ℕ) := finite n → α

def filled (n : ℕ) := ∥finite n∥

def network (α : Type u) := graph (@neq α)

@[hott] def network.decode {α : Type u} (H : prop α) : network α → α := begin
  fapply graph.ind,
  { exact id },
  { intros x y G, apply ground_zero.proto.empty.elim,
    apply G, apply H }
end

@[hott] def network.prop {α : Type u} (H : prop α) : prop (network α) := begin
  intros x y, fapply graph.ind _ _ x; clear x; intro x,
  { fapply graph.ind _ _ y; clear y; intro y,
    { apply Id.map, apply H },
    { intros z G, apply ground_zero.proto.empty.elim,
      apply G, apply H } },
  { intros z G, apply ground_zero.proto.empty.elim,
    apply G, apply H }
end

@[hott] def network.proplem {α : Type u} (H : prop α) : α ≃ network α := begin
  apply ground_zero.structures.prop_equiv_lemma,
  apply H, apply network.prop H,
  apply graph.elem, apply network.decode H
end

def hull (n : ℕ) := network (finite n)
def hull.elem {n : ℕ} : finite n → hull n := graph.elem

end ground_zero.HITs