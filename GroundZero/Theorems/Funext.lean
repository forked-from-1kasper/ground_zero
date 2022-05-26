import GroundZero.Types.HEq
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

  @[hottAxiom] def seg : i₀ = i₁ :=
  GroundZero.Support.inclusion (Quot.sound (I.rel.mk false true))

  instance : OfNat I Nat.zero := ⟨i₀⟩
  instance : OfNat I (Nat.succ Nat.zero) := ⟨i₁⟩

  def left := i₀
  def right := i₁

  def zero := i₀
  def one := i₁

  @[hottAxiom, eliminator] def ind {π : I → Type u} (b₀ : π i₀) (b₁ : π i₁) (s : b₀ =[seg] b₁) (x : I) : π x :=
  begin
    refine Quot.hrecOn x ?_ ?_; apply λ x, @Bool.casesOn (π ∘ discrete) x b₀ b₁;
    { intros a b; induction a <;> induction b <;> intro H;
      { apply HEq.refl };
      { apply @HEq.fromPathover I π _ _ seg _ _ s };
      { apply HEq.symm; apply @HEq.fromPathover I π _ _ seg _ _ s };
      { apply HEq.refl } }
  end

  @[inline] hott def rec {β : Type u} (b₀ : β) (b₁ : β) (s : b₀ = b₁) : I → β :=
  ind b₀ b₁ (Equiv.pathoverOfEq seg s)

  axiom indβrule {π : I → Type u} (b₀ : π i₀) (b₁ : π i₁)
    (s : b₀ =[seg] b₁) : Equiv.apd (ind b₀ b₁ s) seg = s

  noncomputable hott def recβrule {π : Type u} (b₀ b₁ : π)
    (s : b₀ = b₁) : Id.map (rec b₀ b₁ s) seg = s :=
  begin
    apply Equiv.pathoverOfEqInj seg; transitivity;
    symmetry; apply Equiv.apdOverConstantFamily; apply indβrule
  end

  hott def homotopy {α : Type u} {β : α → Type v} {f g : Π x, β x}
    (p : f ~ g) (x : α) : I → β x :=
  Interval.rec (f x) (g x) (p x)

  hott def funext {α : Type u} {β : α → Type v}
    {f g : Π x, β x} (p : f ~ g) : f = g :=
  @Id.map I (Π x, β x) 0 1 (λ i x, homotopy p x i) seg

  hott def happly {α : Type u} {β : α → Type v}
    {f g : Π x, β x} (p : f = g) : f ~ g :=
  Equiv.transport (λ g, f ~ g) p (Equiv.Homotopy.id f)

  hott def map_happly {α β γ : Type u} {a b : α} {c : β} (f : α → β → γ)
    (p : a = b) : Id.map (f · c) p = happly (Id.map f p) c :=
  begin induction p; reflexivity end
end Interval

end GroundZero.HITs