import ground_zero.types.product
open ground_zero.HITs ground_zero.types
open ground_zero.HITs.interval (i₀ i₁ seg)

/-
  * n-cube.
  * Path (1-cube).
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

def Path {α : Type u} (a b : α) := Cube 0 (a, b)
def Path.lam {α : Type u} (f : I → α) : Path (f 0) (f 1) :=
Cube.lam f

@[hott] def Path.rec {α : Type u} {C : Π (a b : α), Path a b → Sort v}
  (h : Π (f : I → α), C (f 0) (f 1) (Path.lam f))
  {a b : α} (p : Path a b) : C a b p :=
@Cube.rec α 0
  (λ x, match x with
  | (a, b) := C a b
  end)
  (by apply h) (a, b) p

abbreviation LineP (σ : I → Type u) := Π (i : I), σ i
abbreviation Line (α : Type u) := I → α
def Line.refl {α : Type u} (a : α) : Line α := λ _, a

@[hott] def decode {α : Type u} {a b : α} (p : a = b :> α) : Path a b :=
Path.lam (interval.elim p)

@[hott] def encode {α : Type u} {a b : α} : Path a b → (a = b :> α) :=
Path.rec (# seg)

@[hott] noncomputable def encode_decode {α : Type u} {a b : α} (p : a = b :> α) :
  encode (decode p) = p :> a = b :> α :=
by apply interval.recβrule

@[hott] def Path.compute {α : Type u} {a b : α} (p : Path a b) : I → α :=
interval.rec a b (encode p)

infix ` # `:40 := Path.compute
notation `<` binder `> ` r:(scoped P, Path.lam P) := r

infix ` ⇝ `:30 := Path

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