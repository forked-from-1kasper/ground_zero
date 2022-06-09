import GroundZero.HITs.Interval
open GroundZero GroundZero.Types GroundZero.Types.Equiv
open GroundZero.HITs GroundZero.HITs.Interval
open GroundZero.Structures

namespace GroundZero.Theorems.Fibration
  universe u v

  hott def forward {A : Type u} {B : A → Type v} (x : A) :
    Types.fib (@Sigma.fst A B) x → B x :=
  λ ⟨⟨y, u⟩, H⟩, subst H u

  hott def left {A : Type u} {B : A → Type v} (x : A) (u : B x) :
    Types.fib (@Sigma.fst A B) x :=
  ⟨⟨x, u⟩, idp _⟩

  hott def fiberOver {A : Type u} {B : A → Type v} (x : A) :
    Types.fib (@Sigma.fst A B) x ≃ B x :=
  begin
    existsi forward x; apply Prod.mk <;> existsi (@left A B x);
    { intro ⟨⟨y, u⟩, (H : y = x)⟩; induction H; apply idp };
    { intro; reflexivity }
  end

  inductive leg {A : Type u} : A → Type u
  | lam (f : I → A) : leg (f 0)

  inductive post {A : Type u} : A → Type u
  | lam (f : I → A) : post (f 1)

  hott def liftingProperty {A : Type u} {B : Type v} (p : A → B) :=
  Π x, leg (p x) → leg x

  hott def Fibration (A : Type u) (B : Type v) :=
  Σ (p : A → B), liftingProperty p

  infix:60 " ↠ " => Fibration

  hott def lifting {A : Type u} {B : A → Type v} (f : I → A) (u : B (f 0)) : @leg (Sigma B) ⟨f 0, u⟩ :=
  @leg.lam (Sigma B) (λ i, ⟨f i, @Interval.ind (B ∘ f) u (subst seg u) (idp _) i⟩)

  hott def typeFamily {A : Type u} (B : A → Type v) : (Σ x, B x) ↠ A :=
  begin existsi Sigma.fst; intro ⟨x, u⟩ f; apply @leg.casesOn A (λ x f, Π u, @leg (Σ x, B x) ⟨x, u⟩) x f; apply lifting end
end GroundZero.Theorems.Fibration