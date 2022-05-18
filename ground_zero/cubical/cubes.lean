import ground_zero.HITs.interval
open ground_zero.HITs ground_zero.types
open ground_zero.HITs.interval (i₀ i₁ seg)

/-
  * n-cube.
  * Square (2-cube).
-/

namespace ground_zero.cubical
universes u v w r

def binary (α : Type u) : ℕ → Type u
|    0    := α × α
| (n + 1) := binary n × binary n

-- cube n represents (n + 1)-cube.
@[hott] def cube (α : Type u) : ℕ → Type u
|    0    := I → α
| (n + 1) := I → cube n

@[hott] def cube.tree {α : Type u} :
  Π {n : ℕ}, cube α n → binary α n
|    0    f := (f 0, f 1)
| (n + 1) f := (cube.tree (f 0), cube.tree (f 1))

inductive Cube {α : Type u} (n : ℕ) : binary α n → Type u
| lam (f : cube α n) : Cube (cube.tree f)

abbreviation Cube.lambda {α : Type u} (n : ℕ)
  (f : cube α n) : Cube n (cube.tree f) :=
Cube.lam f

/-
     c ------> d
     ^         ^
     |         |
     |         |
     |         |
     a ------> b
-/
@[hott] def Square {α : Type u} (a b c d : α) :=
Cube 1 ((a, b), (c, d))

def Square.lam {α : Type u} (f : I → I → α) :
  Square (f 0 0) (f 0 1) (f 1 0) (f 1 1) :=
Cube.lam f

@[hott] def Square.rec {α : Type u}
  {C : Π (a b c d : α), Square a b c d → Type v}
  (h : Π (f : I → I → α), C (f 0 0) (f 0 1) (f 1 0) (f 1 1) (Square.lam f))
  {a b c d : α} (τ : Square a b c d) : C a b c d τ :=
@Cube.rec α 1
  (λ x, match x with
  | ((a, b), (c, d)) := C a b c d
  end)
  (by apply h) ((a, b), (c, d)) τ

end ground_zero.cubical