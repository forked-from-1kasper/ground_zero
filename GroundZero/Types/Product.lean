import GroundZero.Theorems.Funext

namespace GroundZero.Types

universe u v u' v' w

namespace Product
  variable {A : Type u} {B : Type v}

  def elim {C : Type w} (g : A → B → C) (x : A × B) : C :=
  g x.pr₁ x.pr₂

  def uniq : Π (x : A × B), (x.pr₁, x.pr₂) = x := idp

  def prod {a b : A} {c d : B} (p : a = b) (q : c = d) : (a, c) = (b, d) :=
  begin induction p; induction q; reflexivity end

  hott def prod' {A : Type u} {B : Type v} (x y : A × B) (p : x.1 = y.1) (q : x.2 = y.2) : x = y :=
  begin apply prod <;> assumption end

  hott def ind {π : A × B → Type w} (g : Π x y, π (x, y)) : Π x, π x := λ w, g w.1 w.2

  hott def univ {ν : Type w} : (ν → A × B) ≃ (ν → A) × (ν → B) :=
  begin
    let e₁ : (ν → A × B) → (ν → A) × (ν → B) :=
    λ f, (Prod.pr₁ ∘ f, Prod.pr₂ ∘ f);
    let e₂ : (ν → A) × (ν → B) → (ν → A × B) :=
    λ f x, (f.pr₁ x, f.pr₂ x);
    existsi e₁; apply Qinv.toBiinv;
    existsi e₂; apply Prod.mk <;> reflexivity
  end

  hott def bimap {C : Type u'} {D : Type v'} (f : A → C) (g : B → D) (w : A × B) : C × D := (f w.1, g w.2)
  hott def swap (w : A × B) : B × A := (w.2, w.1)

  hott def comm : A × B ≃ B × A :=
  ⟨swap, (⟨swap, idp⟩, ⟨swap, idp⟩)⟩

  instance {A : Type u} {B : Type v}
    [OfNat A 1] [OfNat B 1] :
    OfNat (A × B) (Nat.succ Nat.zero) :=
  ⟨(1, 1)⟩
end Product

end GroundZero.Types