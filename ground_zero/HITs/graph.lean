import ground_zero.HITs.truncation
open ground_zero.types ground_zero.types.eq (renaming rfl -> idp)

hott theory

namespace ground_zero.HITs

universes u v w
inductive graph.rel {α : Sort u} (edges : α → α → Sort v) : α → α → Prop
| line {n m : α} : edges n m → graph.rel n m

def graph {α : Sort u} (edges : α → α → Sort v) := quot (graph.rel edges)

namespace graph
  def elem {α : Sort u} {edges : α → α → Sort w} : α → graph edges :=
  quot.mk (rel edges)

  def line {α : Sort u} {edges : α → α → Sort w} {x y : α}
    (h : edges x y) : @elem α edges x = @elem α edges y :=
  ground_zero.support.inclusion (quot.sound (rel.line h))

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
  | Kneiphof Lomse    := ground_zero.types.unit
  | Altstadt Lomse    := ground_zero.types.unit
  | Lomse    Vorstadt := ground_zero.types.unit
  | Altstadt Kneiphof := bool
  | Altstadt Vorstadt := bool
  | _        _        := empty
end Koenigsberg

structure precategory (α : Sort u) :=
(hom : α → α → Sort v)
(id {a : α} : hom a a)
(comp {a b c : α} : hom b c → hom a b → hom a c)
(infix ∘ := comp)
(id_left {a b : α} : Π (f : hom a b), f = id ∘ f)
(id_right {a b : α} : Π (f : hom a b), f = f ∘ id)
(assoc {a b c d : α} : Π (f : hom a b) (g : hom b c) (h : hom c d),
  h ∘ (g ∘ f) = (h ∘ g) ∘ f)

def cat_graph {α : Sort u} (C : precategory α) := graph C.hom

end ground_zero.HITs