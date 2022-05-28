import GroundZero.Theorems.Funext

namespace GroundZero.Types

universe u v u' v' w

namespace product
  variable {α : Type u} {β : Type v}

  def elim {γ : Type w} (g : α → β → γ) (x : α × β) : γ :=
  g x.pr₁ x.pr₂

  def uniq : Π (x : α × β), (x.pr₁, x.pr₂) = x := idp

  def prod (a b : α) (c d : β) (p : a = b) (q : c = d) : (a, c) = (b, d) :=
  begin induction p; induction q; reflexivity end

  hott def prod' {α : Type u} {β : Type v} (x y : α × β) (p : x.1 = y.1) (q : x.2 = y.2) : x = y :=
  begin apply prod <;> assumption end

  hott def ind {π : α × β → Type w} (g : Π x y, π (x, y)) : Π x, π x := λ w, g w.1 w.2

  hott def univ {ν : Type w} : (ν → α × β) ≃ (ν → α) × (ν → β) :=
  begin
    let e₁ : (ν → α × β) → (ν → α) × (ν → β) :=
    λ f, (Prod.pr₁ ∘ f, Prod.pr₂ ∘ f);
    let e₂ : (ν → α) × (ν → β) → (ν → α × β) :=
    λ f x, (f.pr₁ x, f.pr₂ x);
    existsi e₁; apply Qinv.toBiinv;
    existsi e₂; apply Prod.mk <;> reflexivity
  end

  hott def bimap {γ : Type u'} {δ : Type v'} (f : α → γ) (g : β → δ) (w : α × β) : γ × δ := (f w.1, g w.2)
  hott def swap (w : α × β) : β × α := (w.2, w.1)

  hott def comm : α × β ≃ β × α :=
  ⟨swap, (⟨swap, idp⟩, ⟨swap, idp⟩)⟩

  instance {α : Type u} {β : Type v}
    [OfNat α 1] [OfNat β 1] :
    OfNat (α × β) (Nat.succ Nat.zero) :=
  ⟨(1, 1)⟩
end product

end GroundZero.Types