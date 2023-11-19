import GroundZero.Types.HEq

open GroundZero.Types.Id (ap)
open GroundZero.Types

/-
  The unit Interval I as Higher Inductive Type.
  Proof of functional extensionality from it.
  * HoTT 6.3

  It is primitive HIT.
  * HoTT, chapter 6, exercise 6.13
-/

namespace GroundZero.HITs
universe u v w

inductive I.rel : 𝟐 → 𝟐 → Prop
| mk (a b : 𝟐) : rel a b

def I : Type := Quot I.rel
def Interval := I

namespace Interval
  hott def discrete : 𝟐 → I := Quot.mk I.rel

  hott def i₀ : I := discrete false
  hott def i₁ : I := discrete true

  @[hottAxiom] opaque seg : i₀ = i₁ :=
  trustHigherCtor (Quot.sound (I.rel.mk false true))

  instance : OfNat I Nat.zero := ⟨i₀⟩
  instance : OfNat I (Nat.succ Nat.zero) := ⟨i₁⟩

  hott def left  := i₀
  hott def right := i₁

  hott def zero := i₀
  hott def one  := i₁

  attribute [reducible] left right zero one

  @[hottAxiom, eliminator] def ind {B : I → Type u} (b₀ : B i₀) (b₁ : B i₁) (s : b₀ =[seg] b₁) (x : I) : B x :=
  begin
    refine Quot.hrecOn x ?_ ?_; apply λ x, @Bool.casesOn (B ∘ discrete) x b₀ b₁;
    { intros a b; induction a <;> induction b <;> intro H;
      { apply HEq.refl };
      { apply @HEq.fromPathover I B _ _ seg _ _ s };
      { apply HEq.symm; apply @HEq.fromPathover I B _ _ seg _ _ s };
      { apply HEq.refl } }
  end

  @[inline] hott def rec {B : Type u} (b₀ : B) (b₁ : B) (s : b₀ = b₁) : I → B :=
  ind b₀ b₁ (Equiv.pathoverOfEq seg s)

  axiom indβrule {B : I → Type u} (b₀ : B i₀) (b₁ : B i₁)
    (s : b₀ =[seg] b₁) : Equiv.apd (ind b₀ b₁ s) seg = s

  noncomputable hott def recβrule {B : Type u} (b₀ b₁ : B)
    (s : b₀ = b₁) : ap (rec b₀ b₁ s) seg = s :=
  begin
    apply Equiv.pathoverOfEqInj seg; transitivity;
    symmetry; apply Equiv.apdOverConstantFamily; apply indβrule
  end

  hott def homotopy {A : Type u} {B : A → Type v} {f g : Π x, B x}
    (p : f ~ g) (x : A) : I → B x :=
  Interval.rec (f x) (g x) (p x)

  hott def funext {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (p : f ~ g) : f = g :=
  @ap I (Π x, B x) 0 1 (λ i x, homotopy p x i) seg

  hott def happly {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (p : f = g) : f ~ g :=
  Equiv.transport (λ g, f ~ g) p (Equiv.Homotopy.id f)

  hott def happlyRev {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (p : f = g) : happly p⁻¹ = Equiv.Homotopy.symm _ _ (happly p) :=
  begin induction p; reflexivity end

  hott def mapHapply {A : Type u} {B : Type v} {C : Type w} {a b : A} {c : B}
    (f : A → B → C) (p : a = b) : ap (f · c) p = happly (ap f p) c :=
  begin induction p; reflexivity end
end Interval

end GroundZero.HITs
