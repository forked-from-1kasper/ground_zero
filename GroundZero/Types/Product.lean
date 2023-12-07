import GroundZero.Theorems.Funext

open GroundZero.Types.Equiv (bimap)
open GroundZero.Types.Id (ap)

namespace GroundZero.Types

universe u v u' v' w

namespace Product
  open Prod (pr₁ pr₂)

  variable {A : Type u} {B : Type v}

  hott definition elim {C : Type w} (g : A → B → C) (x : A × B) : C :=
  g x.pr₁ x.pr₂

  hott remark uniq : Π (x : A × B), (x.pr₁, x.pr₂) = x := idp

  hott definition prod {a b : A} {c d : B} (p : a = b) (q : c = d) : (a, c) = (b, d) :=
  begin induction p; induction q; reflexivity end

  hott definition eqOfProdEq {w₁ w₂ : A × B} (ω : w₁.1 = w₂.1 × w₁.2 = w₂.2) : w₁ = w₂ :=
  prod ω.1 ω.2

  hott lemma apFstProd {a b : A} {c d : B} (p : a = b) (q : c = d) : ap pr₁ (prod p q) = p :=
  begin induction p; induction q; reflexivity end

  hott lemma apSndProd {a b : A} {c d : B} (p : a = b) (q : c = d) : ap pr₂ (prod p q) = q :=
  begin induction p; induction q; reflexivity end

  hott corollary apFst {w₁ w₂ : A × B} (ω : w₁.1 = w₂.1 × w₁.2 = w₂.2) : ap pr₁ (eqOfProdEq ω) = ω.1 :=
  apFstProd ω.1 ω.2

  hott corollary apSnd {w₁ w₂ : A × B} (ω : w₁.1 = w₂.1 × w₁.2 = w₂.2) : ap pr₂ (eqOfProdEq ω) = ω.2 :=
  apSndProd ω.1 ω.2

  hott lemma mapProd {C : Type w} {a₁ a₂ : A} {b₁ b₂ : B} (f : A → B → C)
    (p : a₁ = a₂) (q : b₁ = b₂) : ap (λ w, f w.1 w.2) (prod p q) = bimap f p q :=
  begin induction p; induction q; reflexivity end

  hott definition prod' {x y : A × B} (p : x.1 = y.1) (q : x.2 = y.2) : x = y :=
  prod p q

  hott definition ind {π : A × B → Type w} (g : Π x y, π (x, y)) : Π x, π x :=
  λ w, g w.1 w.2

  hott theorem univ {ν : Type w} : (ν → A × B) ≃ (ν → A) × (ν → B) :=
  begin
    let e₁ : (ν → A × B) → (ν → A) × (ν → B) :=
    λ f, (Prod.pr₁ ∘ f, Prod.pr₂ ∘ f);
    let e₂ : (ν → A) × (ν → B) → (ν → A × B) :=
    λ f x, (f.pr₁ x, f.pr₂ x);
    existsi e₁; apply Qinv.toBiinv;
    existsi e₂; apply Prod.mk <;> reflexivity
  end

  hott definition bimap {C : Type u'} {D : Type v'} (f : A → C) (g : B → D) (w : A × B) : C × D := (f w.1, g w.2)

  hott definition swap (w : A × B) : B × A := (w.2, w.1)

  hott lemma comm : A × B ≃ B × A :=
  ⟨swap, (⟨swap, idp⟩, ⟨swap, idp⟩)⟩

  instance {A : Type u} {B : Type v}
    [OfNat A 1] [OfNat B 1] :
    OfNat (A × B) (Nat.succ Nat.zero) :=
  ⟨(1, 1)⟩
end Product

end GroundZero.Types
