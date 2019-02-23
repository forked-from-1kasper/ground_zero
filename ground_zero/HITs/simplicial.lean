import ground_zero.HITs.truncation
open ground_zero.types
open ground_zero.types.eq (renaming rfl -> idp)

/-
  * Filled simplex.
  * Simplex.
-/

hott theory

namespace ground_zero.HITs
universes u v w

def iterated_unit : ℕ → Type
| 0 := empty
| (n + 1) := coproduct ground_zero.types.unit.{1} (iterated_unit n)

def filled_simplex (n : ℕ) := ∥iterated_unit n∥

inductive simplex.core : ℕ → Type
| base {n : ℕ} : simplex.core (n + 1)
| lift {n : ℕ} : simplex.core n → simplex.core (n + 1)

inductive simplex.rel : Π n, simplex.core n → simplex.core n → Prop
| mk {n : ℕ} (x : simplex.core n) :
  simplex.rel (n + 1) simplex.core.base (simplex.core.lift x)

def simplex (n : ℕ) := quot (simplex.rel n)

inductive graph.rel {α : Sort u} (edges : α → α → Sort v) : α → α → Prop
| line (n m : α) : edges n m → graph.rel n m

def graph {α : Sort u} (edges : α → α → Sort v) := quot (graph.rel edges)

namespace graph
  def elem {α : Sort u} {edges : α → α → Sort w} : α → graph edges :=
  quot.mk (rel edges)

  def line {α : Sort u} {edges : α → α → Sort w} {x y : α}
    (h : edges x y) : @elem α edges x = @elem α edges y :=
  ground_zero.support.inclusion (quot.sound (rel.line x y h))

  def rec {α : Sort u} {β : Sort v} {edges : α → α → Sort w}
    (f : α → β) (h : Π x y, edges x y → f x = f y) : graph edges → β := begin
    fapply quot.lift, exact f,
    { intros a b, intro H, cases H,
      apply ground_zero.support.truncation,
      fapply h, assumption }
  end

  def ind {α : Sort u} {edges : α → α → Sort w} {β : graph edges → Sort v}
    (f : Π x, β (elem x)) (h : Π x y (H : edges x y), f x =[line H] f y) :
    Π x, β x := begin
    intro x, fapply quot.hrec_on x,
    exact f, intros a b H, cases H,
    apply ground_zero.types.heq.from_pathover (line H_a),
    fapply h
  end
end graph

def is_connected {α : Sort u} := Σ' (x : α), Π y, ∥x = y∥
def is_loop {α : Sort u} {a : α} (p : a = a) := ¬(p = idp)

inductive Koenigsberg
| Altstadt | Kneiphof
| Lomse    | Vorstadt

namespace Koenigsberg
  def edges : Koenigsberg → Koenigsberg → Type
  | Kneiphof Lomse    := ground_zero.types.unit
  | Altstadt Lomse    := ground_zero.types.unit
  | Lomse    Vorstadt := ground_zero.types.unit
  | Altstadt Kneiphof := bool
  | Altstadt Vorstadt := bool
  | _        _        := empty
end Koenigsberg

end ground_zero.HITs