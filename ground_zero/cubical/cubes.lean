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

def from_equality {α : Sort u} {a b : α} (p : a = b :> α) : Path a b :=
Path.lam (interval.rec a b p)

def to_equality {α : Sort u} {a b : α} (p : Path a b) : a = b :> α :=
@Cube.rec α 0 (begin intros B p, cases B with a b, exact a = b :> α end)
  (λ f, f # seg) (binary.leaf a b) p

def compute {α : Sort u} {a b : α} (p : Path a b) : I → α :=
interval.rec a b (to_equality p)

infix ` # `:40 := compute
notation `<` binder `> ` r:(scoped P, Path.lam P) := r

infix ` ⇝ `:30 := Path

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
def Square {α : Sort u} (m n : I → α)
  (o : m i₀ ⇝ n i₀) (p : m i₁ ⇝ n i₁) :=
Cube 1 (binary.node (binary.leaf (m i₀) (n i₀))
                    (binary.leaf (m i₁) (n i₁)))

end ground_zero.cubical.cubes