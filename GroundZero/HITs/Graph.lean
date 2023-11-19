import GroundZero.Types.HEq

open GroundZero.Types.Equiv (apd)
open GroundZero.Types.Id (ap)
open GroundZero.Types

namespace GroundZero.HITs
universe u v w

inductive Graph.rel {A : Type u} (R : A → A → Type v) : A → A → Prop
| line {n m : A} : R n m → rel R n m

def Graph {A : Type u} (R : A → A → Type v) := Quot (Graph.rel R)

namespace Graph
  hott def elem {A : Type u} {R : A → A → Type w} : A → Graph R :=
  Quot.mk (rel R)

  opaque line {A : Type u} {R : A → A → Type w} {x y : A}
    (h : R x y) : @elem A R x = @elem A R y :=
  trustHigherCtor (Quot.sound (rel.line h))

  def rec {A : Type u} {B : Type v} {R : A → A → Type w}
    (f : A → B) (H : Π x y, R x y → f x = f y) : Graph R → B :=
  begin
    apply Quot.lift f; intro a b H; induction H;
    apply elimEq; apply H; assumption
  end

  @[eliminator] def ind {A : Type u} {R : A → A → Type w} {B : Graph R → Type v}
    (elemβ : Π x, B (elem x)) (lineβ : Π x y (H : R x y), elemβ x =[line H] elemβ y) : Π x, B x :=
  begin
    intro x; apply Quot.hrecOn x elemβ; intros a b H; induction H;
    apply HEq.fromPathover (line _) (lineβ a b _); assumption
  end

  opaque recβrule {A : Type u} {B : Type v} {R : A → A → Type w}
    (f : A → B) (h : Π x y, R x y → f x = f y) {x y : A} (g : R x y) :
    ap (rec f h) (line g) = h x y g :=
  trustCoherence

  opaque indβrule {A : Type u} {R : A → A → Type w} {B : Graph R → Type v}
    (f : Π x, B (elem x)) (h : Π x y (H : R x y), f x =[line H] f y)
    {x y : A} (g : R x y) : apd (ind f h) (line g) = h x y g :=
  trustCoherence

  attribute [irreducible] Graph

  attribute [hottAxiom] Graph elem line rec ind recβrule indβrule
end Graph

end GroundZero.HITs
