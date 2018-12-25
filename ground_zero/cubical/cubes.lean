import ground_zero.types.product
open ground_zero.HITs ground_zero.types
open ground_zero.HITs.interval (i₀ i₁ seg)

namespace ground_zero.cubical.cubes
universes u v w r

inductive binary (α : Sort u) : ℕ → Type u
| leaf {} : α → α → binary 0
| node {n : ℕ} : binary n → binary n → binary (n + 1)

def interval_cube : ℕ → Type
| 0 := I
| (n + 1) := interval_cube n × I

def construct_cube {α : Sort u} :
  Π {n : ℕ}, (interval_cube n → α) → binary α n
| 0 f := binary.leaf (f i₀) (f i₁)
| (n + 1) f := binary.node
  (construct_cube (λ n, f ⟨n, i₀⟩))
  (construct_cube (λ n, f ⟨n, i₁⟩))

inductive Cube {α : Sort u} (n : ℕ) : binary α n → Type u
| lam (f : interval_cube n → α) : Cube (construct_cube f)

def Path {α : Sort u} (a b : α) := Cube 0 (binary.leaf a b)
def Path.lam {α : Sort u} (f : I → α) : Path (f i₀) (f i₁) :=
Cube.lam f

abbreviation LineP (σ : I → Sort u) := Π (i : I), σ i
abbreviation Line (α : Sort u) := I → α
def Line.refl {α : Sort u} (a : α) : Line α := λ _, a

def Square {α : Sort u} (a b c d : α) :=
Cube 1 (binary.node (binary.leaf a b) (binary.leaf c d))
def Square.lam {α : Sort u} (f : I → I → α) :
  Square (f i₀ i₀) (f i₁ i₀) (f i₀ i₁) (f i₁ i₁) :=
Cube.lam (λ (x : interval_cube 1), product.elim f x)

def from_equality {α : Sort u} {a b : α} (p : a = b :> α) : Path a b :=
Path.lam (interval.rec a b p)

def to_equality {α : Sort u} {a b : α} (p : Path a b) : a = b :> α :=
@Cube.rec α 0 (begin intros B p, cases B with a b, exact a = b :> α end)
  (λ f, f # seg) (binary.leaf a b) p

def compute {α : Sort u} {a b : α} (p : Path a b) : I → α :=
interval.rec a b (to_equality p)

def coe (π : I → Sort u) (x : π i₀) : Π i, π i :=
interval.ind x (equiv.subst seg x) eq.rfl

infix ` # `:40 := compute
notation `<` binder `> ` r:(scoped P, Path.lam P) := r

/-
                     p
          a -----------------> b
          ^                    ^
          |                    |
          |                    |
    <j> a |     conn_and p     | p
          |                    |
          |                    |
          |                    |
          a -----------------> a
                   <i> a
  vertices are written from left to right, from bottom to top:
    Square a a a b
-/
infix ` ⇝ `:30 := Path

def Square.and {α : Sort u} {a b : α}
  (p : a ⇝ b) : Square a a a b :=
Square.lam (λ i j, p # i ∧ j)

def Square.const {α : Sort u} (a : α) :
  Square a a a a :=
Square.lam (λ i j, a)

structure tetrad (α : Sort u) (β : Sort v) (γ : Sort r) (δ : Sort w) :=
(one : α) (two : β) (three : γ) (four : δ)

--         u
--    a₀ -----> a₁
--    |         |
-- r­₀ |         | r₁
--    |         |
--    V         V
--    b₀ -----> b₁
--         v
def Square.extract {α : Sort u} {a b c d : α}
  (s : Square a b c d) : tetrad (a ⇝ b) (b ⇝ c) (c ⇝ d) (a ⇝ d) :=
begin
  cases s with f, split,
  exact <i> f ⟨i, i₀⟩, exact <i> f ⟨−i, i⟩,
  exact <i> f ⟨i, i₁⟩, exact <i> f ⟨i, i⟩
end

end ground_zero.cubical.cubes