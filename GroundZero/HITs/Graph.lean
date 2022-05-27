import GroundZero.Types.HEq
open GroundZero.Types

namespace GroundZero.HITs
universe u v w

inductive Graph.rel {α : Type u} (R : α → α → Type v) : α → α → Prop
| line {n m : α} : R n m → rel R n m

def Graph {α : Type u} (R : α → α → Type v) := Quot (Graph.rel R)

namespace Graph
  hott def elem {α : Type u} {R : α → α → Type w} : α → Graph R :=
  Quot.mk (rel R)

  @[hottAxiom] def line {α : Type u} {R : α → α → Type w} {x y : α}
    (h : R x y) : @elem α R x = @elem α R y :=
  GroundZero.Support.inclusion (Quot.sound (rel.line h))

  @[hottAxiom] def rec {α : Type u} {β : Type v} {R : α → α → Type w}
    (f : α → β) (h : Π x y, R x y → f x = f y) : Graph R → β :=
  begin
    apply Quot.lift f; intro a b H; induction H;
    apply GroundZero.Support.truncation;
    apply h; assumption
  end

  @[hottAxiom, eliminator] def ind {α : Type u} {R : α → α → Type w} {β : Graph R → Type v}
    (elemβ : Π x, β (elem x)) (lineβ : Π x y (H : R x y), elemβ x =[line H] elemβ y) : Π x, β x :=
  begin
    intro x; apply Quot.hrecOn x elemβ; intros a b H; induction H;
    apply HEq.fromPathover (line _) (lineβ a b _); assumption
  end

  axiom recβrule {α : Type u} {β : Type v} {R : α → α → Type w}
    (f : α → β) (h : Π x y, R x y → f x = f y) {x y : α} (g : R x y) :
    Id.map (rec f h) (line g) = h x y g

  axiom indβrule {α : Type u} {R : α → α → Type w} {β : Graph R → Type v}
    (f : Π x, β (elem x)) (h : Π x y (H : R x y), f x =[line H] f y)
    {x y : α} (g : R x y) : Equiv.apd (ind f h) (line g) = h x y g
end Graph

end GroundZero.HITs