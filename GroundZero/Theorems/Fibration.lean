import GroundZero.HITs.Interval
open GroundZero GroundZero.Types GroundZero.Types.Equiv
open GroundZero.HITs GroundZero.HITs.Interval
open GroundZero.Structures

namespace GroundZero.Theorems.Fibration
  universe u v

  hott definition forward {A : Type u} {B : A → Type v} (x : A) :
    fib (@Sigma.fst A B) x → B x :=
  λ ⟨⟨y, u⟩, H⟩, transport B H u

  hott definition left {A : Type u} {B : A → Type v} (x : A) (u : B x) :
    fib (@Sigma.fst A B) x :=
  ⟨⟨x, u⟩, idp _⟩

  hott definition fiberOver {A : Type u} {B : A → Type v} (x : A) :
    fib (@Sigma.fst A B) x ≃ B x :=
  begin
    existsi forward x; apply Prod.mk <;> existsi (@left A B x);
    { intro ⟨⟨y, u⟩, (H : y = x)⟩; induction H; apply idp };
    { intro; reflexivity }
  end

  inductive Left {A : Type u} : A → Type u
  | lam (f : I → A) : Left (f 0)

  inductive Right {A : Type u} : A → Type u
  | lam (f : I → A) : Right (f 1)

  hott definition hasLifting {A : Type u} {B : Type v} (f : A → B) :=
  Π x, Left (f x) → Left x

  hott definition Fibration (A : Type u) (B : Type v) :=
  Σ (f : A → B), hasLifting f

  infix:60 " ↠ " => Fibration

  hott definition lifting {A : Type u} {B : A → Type v} (f : I → A) (u : B (f 0)) : @Left (Σ x, B x) ⟨f 0, u⟩ :=
  @Left.lam (Sigma B) (λ i, ⟨f i, transport (B ∘ f) (Interval.contrLeft i) u⟩)

  hott definition typeFamily {A : Type u} (B : A → Type v) : (Σ x, B x) ↠ A :=
  begin existsi Sigma.fst; intro ⟨x, u⟩ f; apply @Left.casesOn A (λ x f, Π u, @Left (Σ x, B x) ⟨x, u⟩) x f; apply lifting end
end GroundZero.Theorems.Fibration
