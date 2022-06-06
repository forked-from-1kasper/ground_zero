import GroundZero.HITs.Interval
open GroundZero GroundZero.Types GroundZero.Types.Equiv
open GroundZero.HITs GroundZero.HITs.Interval
open GroundZero.Structures

namespace GroundZero.Theorems.Fibration
  universe u v

  hott def forward {α : Type u} {β : α → Type v} (x : α) :
    Types.fib (@Sigma.fst α β) x → β x :=
  λ ⟨⟨y, u⟩, H⟩, subst H u

  hott def left {α : Type u} {β : α → Type v} (x : α) (u : β x) :
    Types.fib (@Sigma.fst α β) x :=
  ⟨⟨x, u⟩, idp _⟩

  hott def fiberOver {α : Type u} {β : α → Type v} (x : α) :
    Types.fib (@Sigma.fst α β) x ≃ β x :=
  begin
    existsi forward x; apply Prod.mk <;> existsi (@left α β x);
    { intro ⟨⟨y, u⟩, (H : y = x)⟩; induction H; apply idp };
    { intro; reflexivity }
  end

  inductive leg {α : Type u} : α → Type u
  | lam (f : I → α) : leg (f 0)

  inductive post {α : Type u} : α → Type u
  | lam (f : I → α) : post (f 1)

  hott def liftingProperty {α : Type u} {β : Type v} (p : α → β) :=
  Π x, leg (p x) → leg x

  hott def Fibration (α : Type u) (β : Type v) :=
  Σ (p : α → β), liftingProperty p

  infix:60 " ↠ " => Fibration

  hott def lifting {α : Type u} {β : α → Type v} (f : I → α) (u : β (f 0)) : @leg (Sigma β) ⟨f 0, u⟩ :=
  @leg.lam (Sigma β) (λ i, ⟨f i, @Interval.ind (β ∘ f) u (subst seg u) (idp _) i⟩)

  hott def typeFamily {α : Type u} (β : α → Type v) : (Σ x, β x) ↠ α :=
  begin existsi Sigma.fst; intro ⟨x, u⟩ f; apply @leg.casesOn α (λ x f, Π u, @leg (Σ x, β x) ⟨x, u⟩) x f; apply lifting end
end GroundZero.Theorems.Fibration