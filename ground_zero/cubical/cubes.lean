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

inductive binary (α : Type u) : ℕ → Type u
| leaf {} : α → α → binary 0
| node {n : ℕ} : binary n → binary n → binary (n + 1)

-- cube n represents (n + 1)-cube.
def cube : ℕ → Type
| 0 := I
| (n + 1) := cube n × I

def cube.tree {α : Type u} :
  Π {n : ℕ}, (cube n → α) → binary α n
| 0 f := binary.leaf (f i₀) (f i₁)
| (n + 1) f := binary.node
  (cube.tree (λ n, f ⟨n, 0⟩))
  (cube.tree (λ n, f ⟨n, 1⟩))

inductive Cube {α : Type u} (n : ℕ) : binary α n → Type u
| lam (f : cube n → α) : Cube (cube.tree f)

abbreviation Cube.lambda {α : Type u} (n : ℕ)
  (f : cube n → α) : Cube n (cube.tree f) :=
Cube.lam f

def Path {α : Type u} (a b : α) := Cube 0 (binary.leaf a b)
def Path.lam {α : Type u} (f : I → α) : Path (f 0) (f 1) :=
Cube.lam f

abbreviation LineP (σ : I → Type u) := Π (i : I), σ i
abbreviation Line (α : Type u) := I → α
def Line.refl {α : Type u} (a : α) : Line α := λ _, a

def from_equality {α : Type u} {a b : α} (p : a = b :> α) : Path a b :=
Path.lam (interval.rec a b p)

def to_equality {α : Type u} {a b : α} (p : Path a b) : a = b :> α :=
begin cases p with f, apply eq.map, exact interval.seg end

def Path.compute {α : Type u} {a b : α} (p : Path a b) : I → α :=
interval.rec a b (to_equality p)

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
def Square {α : Type u} (m n : I → α)
  (o : m 0 ⇝ n 0) (p : m 1 ⇝ n 1) :=
Cube 1 (binary.node (binary.leaf (m 0) (n 0))
                    (binary.leaf (m 1) (n 1)))

end ground_zero.cubical