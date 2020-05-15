import ground_zero.HITs.merely ground_zero.types.integer
open ground_zero (iter vect vect.map vect.constant)
open ground_zero.types.eq (renaming rfl -> idp)
open ground_zero.structures (prop)
open ground_zero.types
open ground_zero

local notation `ℤ` := ground_zero.types.integer

hott theory

namespace ground_zero.HITs
universes u v w

def neq {α : Type u} (a b : α) : Type u := a = b → (𝟎 : Type)

def fin := iter 𝟏 𝟏
def filled (n : ℕ) := ∥fin n∥

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
    { apply eq.map, apply H },
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

def hull (n : ℕ) := network (fin n)
def hull.elem {n : ℕ} : fin n → hull n := graph.elem

abbreviation simplex (α : Type u) := list α
def face {α : Type u} (xs : simplex α) (i : ℕ) : simplex α :=
list.take i xs ++ list.drop (i + 1) xs

def enum.aux {α : Type u} : ℕ → list α → list ℕ
| _    []     := []
| n (x :: xs) := n :: enum.aux (n + 1) xs
def enum {α : Type u} := @enum.aux α 0

def faces {α : Type u} (xs : simplex α) : list (simplex α) :=
list.map (face xs) (enum xs)

inductive simplex.nonempty {α : Type u} : simplex α → Type u
| intro (x : α) (xs : simplex α) : simplex.nonempty (x :: xs)
open simplex (nonempty)

def simplex.head {α : Type u} : Π (v : simplex α), nonempty v → α
| (x :: xs) _ := x

def simplex.tail {α : Type u} : Π (v : simplex α), nonempty v → simplex α
| (x :: xs) _ := xs

def faces.nonempty {α : Type u} : Π (v : simplex α), nonempty v → nonempty (faces v) :=
begin intros v H, induction H with y ys, apply simplex.nonempty.intro end

end ground_zero.HITs