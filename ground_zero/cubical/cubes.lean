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
@Cube.rec α 0 (begin intros x q, induction x with a b, exact C a b q end)
  (by apply h) (a, b) p

abbreviation LineP (σ : I → Type u) := Π (i : I), σ i
abbreviation Line (α : Type u) := I → α
def Line.refl {α : Type u} (a : α) : Line α := λ _, a

@[hott] def decode {α : Type u} {a b : α} (p : a = b :> α) : Path a b :=
Path.lam (interval.rec a b p)

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

structure tetrad (α : Type u) (β : Type v) (γ : Type r) (δ : Type w) :=
(one : α) (two : β) (three : γ) (four : δ)

/-
https://github.com/RedPRL/redtt/blob/master/library/prelude/path.red#L13
       <i> n i
    n 0 -----> n 1
     ^          ^
     |          |
   o |          | p
     |          |
    m 0 -----> m 1
       <i> m i
-/
@[hott] def Square {α : Type u} (m n : I → α)
  (o : m 0 ⇝ n 0) (p : m 1 ⇝ n 1) :=
Cube 1 ((m 0, m 1), (n 0, n 1))

end ground_zero.cubical