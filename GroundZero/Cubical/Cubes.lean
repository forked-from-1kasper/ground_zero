import GroundZero.HITs.Interval
open GroundZero.HITs GroundZero.Types
open GroundZero.HITs.Interval (i₀ i₁ seg)

/-
  * n-cube.
  * Square (2-cube).
-/

namespace GroundZero.Cubical
universe u v w r

def binary (α : Type u) : ℕ → Type u
| Nat.zero   => α × α
| Nat.succ n => binary α n × binary α n

-- cube n represents (n + 1)-cube.
hott def cube (α : Type u) : ℕ → Type u
| Nat.zero   => I → α
| Nat.succ n => I → cube α n

hott def cube.tree {α : Type u} : Π {n : ℕ}, cube α n → binary α n
| Nat.zero,   f => (f 0, f 1)
| Nat.succ n, f => (tree (f 0), tree (f 1))

inductive Cube {α : Type u} (n : ℕ) : binary α n → Type u
| lam (f : cube α n) : Cube n (cube.tree f)

def Cube.lambda {α : Type u} (n : ℕ) (f : cube α n) : Cube n (cube.tree f) :=
Cube.lam f

/-
     c ------> d
     ^         ^
     |         |
     |         |
     |         |
     a ------> b
-/
hott def Square {α : Type u} (a b c d : α) :=
Cube 1 ((a, b), (c, d))

def Square.lam {α : Type u} (f : I → I → α) :
  Square (f 0 0) (f 0 1) (f 1 0) (f 1 1) :=
@Cube.lam α 1 f

hott def Square.rec {α : Type u} {C : Π (a b c d : α), Square a b c d → Type v}
  (H : Π (f : I → I → α), C (f 0 0) (f 0 1) (f 1 0) (f 1 1) (Square.lam f))
  {a b c d : α} (τ : Square a b c d) : C a b c d τ :=
@Cube.casesOn α 1 (λ w, C w.1.1 w.1.2 w.2.1 w.2.2) ((a, b), (c, d)) τ H

end GroundZero.Cubical