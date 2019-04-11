import ground_zero.types.heq
open ground_zero.types

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