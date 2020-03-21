import ground_zero.types.heq
open ground_zero.types

hott theory

namespace ground_zero.HITs
universes u v w

inductive graph.rel {α : Type u} (R : α → α → Type v) : α → α → Prop
| line {n m : α} : R n m → graph.rel n m

def graph {α : Type u} (R : α → α → Type v) := quot (graph.rel R)

namespace graph
  @[hott] def elem {α : Type u} {R : α → α → Type w} : α → graph R :=
  quot.mk (rel R)

  @[safe] def line {α : Type u} {R : α → α → Type w} {x y : α}
    (h : R x y) : @elem α R x = @elem α R y :=
  ground_zero.support.inclusion (quot.sound (rel.line h))

  @[safe] def rec {α : Type u} {β : Type v} {R : α → α → Type w}
    (f : α → β) (h : Π x y, R x y → f x = f y) : graph R → β := begin
    fapply quot.lift, exact f,
    { intros a b, intro H, cases H,
      apply ground_zero.support.truncation,
      fapply h, assumption }
  end

  @[safe] def ind {α : Type u} {R : α → α → Type w} {β : graph R → Type v}
    (f : Π x, β (elem x)) (h : Π x y (H : R x y), f x =[line H] f y) :
    Π x, β x := begin
    intro x, fapply quot.hrec_on x,
    exact f, intros a b H, cases H,
    apply ground_zero.types.heq.from_pathover (line H_a),
    fapply h
  end

  axiom recβrule {α : Type u} {β : Type v} {R : α → α → Type w}
    (f : α → β) (h : Π x y, R x y → f x = f y)
    {x y : α} (g : R x y) :
    (rec f h) # (line g) = h x y g

  axiom indβrule {α : Type u} {R : α → α → Type w} {β : graph R → Type v}
    (f : Π x, β (elem x)) (h : Π x y (H : R x y), f x =[line H] f y)
    {x y : α} (g : R x y) :
    equiv.apd (ind f h) (line g) = h x y g
end graph

end ground_zero.HITs