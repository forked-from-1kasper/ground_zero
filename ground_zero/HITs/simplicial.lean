import ground_zero.HITs.merely
open ground_zero.types.eq (renaming rfl -> idp)
open ground_zero.structures (prop)
open ground_zero.types

hott theory

namespace ground_zero.HITs
universes u v w

def neq {α : Type u} (a b : α) : Type u := a = b → (𝟎 : Type)

def fin : ℕ → Type
| 0 := empty
| (n + 1) := coproduct ground_zero.types.unit.{0} (fin n)

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

end ground_zero.HITs