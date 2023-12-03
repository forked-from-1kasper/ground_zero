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
  λ x, Quot.withUseOf H (Quot.lift f (λ a b, λ (Graph.rel.line ε), elimEq (H a b ε)) x) x

  @[eliminator] def ind {A : Type u} {R : A → A → Type v} {B : Graph R → Type w}
    (f : Π x, B (elem x)) (ε : Π x y H, f x =[line H] f y) : Π x, B x :=
  λ x, Quot.withUseOf ε (Quot.hrecOn x f (λ a b, λ (Graph.rel.line H), HEq.fromPathover (line H) (ε a b H))) x

  opaque recβrule {A : Type u} {B : Type v} {R : A → A → Type w}
    (f : A → B) (h : Π x y, R x y → f x = f y) {x y : A}
    (g : R x y) : ap (rec f h) (line g) = h x y g :=
  trustCoherence

  opaque indβrule {A : Type u} {R : A → A → Type v} {B : Graph R → Type w}
    (f : Π x, B (elem x)) (h : Π x y (H : R x y), f x =[line H] f y)
    {x y : A} (g : R x y) : apd (ind f h) (line g) = h x y g :=
  trustCoherence

  attribute [irreducible] Graph

  attribute [hottAxiom] Graph elem line rec ind recβrule indβrule
end Graph

end GroundZero.HITs
