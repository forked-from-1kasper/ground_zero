import ground_zero.types.heq
open ground_zero.types

hott theory

namespace ground_zero.HITs
universes u v w

inductive graph.rel {α : Sort u} (R : α → α → Sort v) : α → α → Prop
| line {n m : α} : R n m → graph.rel n m

def graph {α : Sort u} (R : α → α → Sort v) := quot (graph.rel R)

namespace graph
  def elem {α : Sort u} {R : α → α → Sort w} : α → graph R :=
  quot.mk (rel R)

  def line {α : Sort u} {R : α → α → Sort w} {x y : α}
    (h : R x y) : @elem α R x = @elem α R y :=
  ground_zero.support.inclusion (quot.sound (rel.line h))

  def rec {α : Sort u} {β : Sort v} {R : α → α → Sort w}
    (f : α → β) (h : Π x y, R x y → f x = f y) : graph R → β := begin
    fapply quot.lift, exact f,
    { intros a b, intro H, cases H,
      apply ground_zero.support.truncation,
      fapply h, assumption }
  end

  def ind {α : Sort u} {R : α → α → Sort w} {β : graph R → Sort v}
    (f : Π x, β (elem x)) (h : Π x y (H : R x y), f x =[line H] f y) :
    Π x, β x := begin
    intro x, fapply quot.hrec_on x,
    exact f, intros a b H, cases H,
    apply ground_zero.types.heq.from_pathover (line H_a),
    fapply h
  end

  axiom recβrule {α : Sort u} {β : Sort v} {R : α → α → Sort w}
    (f : α → β) (h : Π x y, R x y → f x = f y)
    {x y : α} (g : R x y) :
    (rec f h) # (line g) = h x y g

  axiom indβrule {α : Sort u} {R : α → α → Sort w} {β : graph R → Sort v}
    (f : Π x, β (elem x)) (h : Π x y (H : R x y), f x =[line H] f y)
    {x y : α} (g : R x y) :
    dep_path.apd (ind f h) (line g) = h x y g
end graph

end ground_zero.HITs