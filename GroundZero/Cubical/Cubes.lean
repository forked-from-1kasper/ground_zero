import GroundZero.HITs.Interval
open GroundZero.HITs GroundZero.Types
open GroundZero.HITs.Interval (i₀ i₁ seg)

/-
  * n-cube.
  * Square (2-cube).
-/

namespace GroundZero.Cubical
universe u v w r

def binary (A : Type u) : ℕ → Type u
| Nat.zero   => A × A
| Nat.succ n => binary A n × binary A n

-- cube n represents (n + 1)-cube.
hott def cube (A : Type u) : ℕ → Type u
| Nat.zero   => I → A
| Nat.succ n => I → cube A n

hott def cube.tree {A : Type u} : Π {n : ℕ}, cube A n → binary A n
| Nat.zero,   f => (f 0, f 1)
| Nat.succ n, f => (tree (f 0), tree (f 1))

inductive Cube {A : Type u} (n : ℕ) : binary A n → Type u
| lam (f : cube A n) : Cube n (cube.tree f)

def Cube.lambda {A : Type u} (n : ℕ) (f : cube A n) : Cube n (cube.tree f) :=
Cube.lam f

/-
     c ------> d
     ^         ^
     |         |
     |         |
     |         |
     a ------> b
-/
hott def Square {A : Type u} (a b c d : A) :=
Cube 1 ((a, b), (c, d))

def Square.lam {A : Type u} (f : I → I → A) :
  Square (f 0 0) (f 0 1) (f 1 0) (f 1 1) :=
@Cube.lam A 1 f

hott def Square.rec {A : Type u} {C : Π (a b c d : A), Square a b c d → Type v}
  (H : Π (f : I → I → A), C (f 0 0) (f 0 1) (f 1 0) (f 1 1) (Square.lam f))
  {a b c d : A} (τ : Square a b c d) : C a b c d τ :=
@Cube.casesOn A 1 (λ w, C w.1.1 w.1.2 w.2.1 w.2.2) ((a, b), (c, d)) τ H

end GroundZero.Cubical