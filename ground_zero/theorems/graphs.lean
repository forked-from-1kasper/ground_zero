import ground_zero.HITs.truncation
open ground_zero.types.eq (renaming rfl -> idp) ground_zero.HITs

hott theory

namespace ground_zero.theorems.graphs
universe u

def is_connected (α : Sort u) := Σ' (x : α), Π y, ∥x = y∥
def is_loop {α : Sort u} {a : α} (p : a = a) := ¬(p = idp)

def is_acyclic {α : Sort u} (edges : α → α → Sort u) :=
ground_zero.structures.K (graph edges)

def is_tree {α : Sort u} (edges : α → α → Sort u) :=
is_connected (graph edges) × is_acyclic edges

def is_complete {α : Sort u} (edges : α → α → Sort u) :=
ground_zero.structures.prop (graph edges)

namespace iso_example
  inductive ABC
  | A | B
  open ABC

  def G₁ : ABC → ABC → Type
  | A B := 𝟐
  | _ _ := 𝟎

  def G₂ : ABC → ABC → Type
  | A B := 𝟏
  | B A := 𝟏
  | _ _ := 𝟎

  def G₁G₂ : graph G₁ → graph G₂ :=
  graph.rec (graph.elem ∘ id) (begin
    intros x y, cases x; cases y; intro H,
    { cases H },
    { cases H,
      { apply graph.line, exact ★ },
      { symmetry, apply graph.line, exact ★ } },
    { cases H },
    { cases H }
  end)
  
  def G₂G₁ : graph G₂ → graph G₁ :=
  graph.rec (graph.elem ∘ id) (begin
    intros x y, cases x; cases y; intro H,
    { cases H },
    { apply graph.line, exact ff },
    { symmetry, apply graph.line, exact tt },
    { cases H }
  end)
end iso_example

inductive Koenigsberg
| Altstadt | Kneiphof
| Lomse    | Vorstadt

namespace Koenigsberg
  def edges : Koenigsberg → Koenigsberg → Type
  | Kneiphof Lomse    := 𝟏
  | Altstadt Lomse    := 𝟏
  | Lomse    Vorstadt := 𝟏
  | Altstadt Kneiphof := 𝟐
  | Altstadt Vorstadt := 𝟐
  | _        _        := 𝟎
end Koenigsberg

end ground_zero.theorems.graphs