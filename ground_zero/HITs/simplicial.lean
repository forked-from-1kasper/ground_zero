import ground_zero.HITs.merely
open ground_zero (iter vect vect.map vect.constant)
open ground_zero.types.eq (renaming rfl -> idp)
open ground_zero.structures (prop)
open ground_zero.types

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

axiom glue {α : Type u} : simplex α → Type u
axiom glue.refl {α : Type u} (a : α) : Π n, glue (list.repeat a n)

def glue.open {α : Type u} (v : simplex α) (H : nonempty v) :=
list.foldl (λ μ face, glue face × μ) 𝟏
           (simplex.tail (faces v) (faces.nonempty v H))

def glue.lid {α : Type u} (v : simplex α) (H : nonempty v) :=
glue (simplex.head (faces v) (faces.nonempty v H))

axiom glue.comp {α : Type u} {v : simplex α} (H : nonempty v) :
  glue.open v H → glue.lid v H

axiom glue.eqv {α : Type u} (v : simplex α) (H : nonempty v) :
  glue v ≃ (Σ top bot, top = glue.comp H bot)

axiom glue.zero {α : Type u}           : 𝟎       ≃ @glue α []
axiom glue.unit {α : Type u} {a : α}   : 𝟏       ≃  glue   [a]
axiom glue.path {α : Type u} {a b : α} : (a = b) ≃  glue   [a, b]

axiom glue.compβ {α : Type u} {a b c : α} (p : a = b) (q : a = c) :
  @glue.comp α [a, b, c] (by apply simplex.nonempty.intro)
    (glue.path.forward p, glue.path.forward q, ★) =
      glue.path.forward (p⁻¹ ⬝ q)

abbreviation complex (α : Type u) := list (simplex α)

axiom K {α : Type u} : complex α → Type u
axiom K.elem {α : Type u} {v : complex α} : α → K v
axiom K.glue {α : Type u} {v : complex α} : Π x, x ∈ v → glue x

end ground_zero.HITs