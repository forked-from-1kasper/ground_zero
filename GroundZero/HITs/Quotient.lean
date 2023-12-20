import GroundZero.Types.HEq

open GroundZero.Types.Equiv (apd)
open GroundZero.Types.Id (ap)
open GroundZero.Types

namespace GroundZero.HITs
universe u v w

inductive Quotient.rel {A : Type u} (R : A → A → Type v) : A → A → Prop
| line {n m : A} : R n m → rel R n m

hott axiom Quotient {A : Type u} (R : A → A → Type v) : Type (max u v) :=
Resize.{u, v} (Quot (Quotient.rel R))

namespace Quotient
  hott axiom elem {A : Type u} {R : A → A → Type w} : A → Quotient R :=
  Resize.intro ∘ Quot.mk (rel R)

  hott opaque axiom line {A : Type u} {R : A → A → Type w} {x y : A}
    (H : R x y) : @elem A R x = @elem A R y :=
  trustHigherCtor (congrArg Resize.intro (Quot.sound (rel.line H)))

  hott axiom rec {A : Type u} {B : Type v} {R : A → A → Type w}
    (f : A → B) (H : Π x y, R x y → f x = f y) : Quotient R → B :=
  λ x, Quot.withUseOf H (Quot.lift f (λ a b, λ (rel.line ε), elimEq (H a b ε)) x.elim) x.elim

  @[eliminator] hott axiom ind {A : Type u} {R : A → A → Type v} {B : Quotient R → Type w}
    (f : Π x, B (elem x)) (ε : Π x y H, f x =[line H] f y) : Π x, B x :=
  λ x, Quot.withUseOf ε (@Quot.hrecOn A (rel R) (B ∘ Resize.intro) x.elim f
    (λ a b, λ (rel.line H), HEq.fromPathover (line H) (ε a b H))) x.elim

  hott opaque axiom recβrule {A : Type u} {B : Type v} {R : A → A → Type w}
    (f : A → B) (ε : Π x y, R x y → f x = f y) {x y : A}
    (g : R x y) : ap (rec f ε) (line g) = ε x y g :=
  trustCoherence

  hott opaque axiom indβrule {A : Type u} {R : A → A → Type v} {B : Quotient R → Type w}
    (f : Π x, B (elem x)) (ε : Π x y H, f x =[line H] f y)
    {x y : A} (g : R x y) : apd (ind f ε) (line g) = ε x y g :=
  trustCoherence

  attribute [irreducible] Quotient

  section
    variable {A : Type u} {R : A → A → Type v} {B : Quotient R → Type w}
             (f : Π x, B (elem x)) (ε₁ ε₂ : Π x y H, f x =[line H] f y)

    #failure ind f ε₁ ≡ ind f ε₂
  end

  section
    variable {A : Type u} {R : A → A → Type v} {B : Type w}
             (f : A → B) (ε₁ ε₂ : Π x y, R x y → f x = f y)

    #failure rec f ε₁ ≡ rec f ε₂
  end
end Quotient

end GroundZero.HITs
