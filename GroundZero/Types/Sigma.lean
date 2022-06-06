import GroundZero.Types.Equiv

namespace GroundZero.Types
universe u v w

namespace Sigma
  variable {A : Type u} {B : A → Type v}

  hott def pr₁ (x : Σ x, B x) := x.1
  hott def pr₂ (x : Σ x, B x) := x.2

  hott def elim {C : Type w} (g : Π x, B x → C) (w : Sigma B) : C := g w.1 w.2

  hott def Ind {π : Sigma B → Type w} (g : Π (a : A) (b : B a), π ⟨a, b⟩) : Π x, π x :=
  λ w, g w.1 w.2

  hott def uniq : Π (x : Σ x, B x), ⟨pr₁ x, pr₂ x⟩ = x := idp

  hott def prod {A : Type u} {B : A → Type v} : Π {u v : Sigma B}
    (p : u.1 = v.1) (q : Equiv.subst p u.2 = v.2), u = v :=
  begin
    intro ⟨x, u⟩ ⟨y, v⟩ (p : x = y); induction p;
    intro (q : u = v); induction q; apply idp
  end

  hott def mapFstOverProd {A : Type u} {B : A → Type v} : Π {u v : Sigma B}
    (p : u.1 = v.1) (q : Equiv.subst p u.snd = v.snd), Id.map pr₁ (prod p q) = p :=
  begin
    intro ⟨x, u⟩ ⟨y, v⟩ (p : x = y); induction p;
    intro (q : u = v); induction q; apply idp
  end

  hott def prodRefl {A : Type u} {B : A → Type v}
    (u : Sigma B) : prod (idp u.1) (idp u.2) = idp u :=
  idp (idp u)

  hott def prodComp {A : Type u} {B : A → Type v} : Π {x y z : Sigma B}
    (p : x.1 = y.1) (q : y.1 = z.1) (r : x.2 =[p] y.2) (s : y.2 =[q] z.2),
    prod (p ⬝ q) (r ⬝′ s) = prod p r ⬝ prod q s :=
  begin
    intro ⟨x, X⟩ ⟨y, Y⟩ ⟨z, Z⟩ (p : x = y) (q : y = z);
    induction p; induction q; intro (r : X = Y) (s : Y = Z);
    induction r; induction s; apply idp
  end

  hott def prodEq {A : Type u} {B : A → Type v} : Π {u v : Sigma B}
    (p p' : u.1 = v.1) (q : Equiv.subst p u.2 = v.2) (q' : Equiv.subst p' u.2 = v.2)
    (r : p = p') (s : q =[λ ρ, Equiv.subst ρ u.2 = v.2, r] q'),
    Sigma.prod p q = Sigma.prod p' q' :=
  begin
    intro ⟨x, u⟩ ⟨y, v⟩ (p : x = y) (p' : x = y) q q' r;
    induction r; induction p; intro (s : q = q'); induction s; apply idp
  end

  hott def spec {A : Type u} {B : Type v} (w : Σ (a : A), B) : A × B := (w.1, w.2)
  hott def gen {A : Type u} {B : Type v} (w : A × B) : Σ (a : A), B := ⟨w.1, w.2⟩

  hott def const (A : Type u) (B : Type v) : (Σ (a : A), B) ≃ A × B :=
  ⟨spec, Qinv.toBiinv _ ⟨gen, (idp, idp)⟩⟩

  hott def hmtpyInv {A : Type v} {B : Type u} (f g : A → B)
    (w : Σ x, f x = g x) : (Σ x, g x = f x) :=
  ⟨w.1, w.2⁻¹⟩

  hott def map {A : Type v} {η : A → Type u} {ε : A → Type w}
    (f : Π x, η x → ε x) (w : Σ x, η x) : (Σ x, ε x) :=
  ⟨w.1, f w.1 w.2⟩

  hott def respectsEquiv {A : Type v} {η : A → Type u} {ε : A → Type w}
    (e : Π x, η x ≃ ε x) : (Σ x, η x) ≃ (Σ x, ε x) :=
  begin
    existsi (map (λ x, (e x).forward)); apply Prod.mk;
    { existsi (map (λ x, (e x).left)); intro w;
      apply Id.map (Sigma.mk w.1); apply (e w.1).leftForward };
    { existsi (map (λ x, (e x).right)); intro w;
      apply Id.map (Sigma.mk w.1); apply (e w.1).forwardRight }
  end

  hott def replaceIshae {A : Type u} {B : Type v} {C : A → Type w}
    (g : B → A) (ρ : Ishae g) : (Σ x, C x) ≃ (Σ x, C (g x)) :=
  begin
    existsi (λ w, ⟨ρ.1 w.1, Equiv.transport C (ρ.2.2.1 w.1)⁻¹ w.2⟩);
    apply Qinv.toBiinv; existsi (λ w, ⟨g w.1, w.2⟩); apply Prod.mk <;> intro w;
    { apply @prod B (C ∘ g) ⟨ρ.1 (g w.1), _⟩ w (ρ.2.1 w.1);
      transitivity; apply Equiv.transportComp;
      transitivity; symmetry; apply Equiv.substComp;
      transitivity; apply Id.map (λ p, Equiv.subst p w.2);
      apply Id.compReflIfEq; symmetry; apply ρ.2.2.2; reflexivity };
    { apply prod; apply Equiv.transportBackAndForward }
  end

  hott def hmtpyInvEqv {A : Type v} {B : Type u} (f g : A → B) :
    (Σ x, f x = g x) ≃ (Σ x, g x = f x) :=
  begin
    existsi hmtpyInv f g; apply Qinv.toBiinv;
    existsi hmtpyInv g f; apply Prod.mk <;>
    { intro w; apply Id.map (Sigma.mk w.1); apply Id.invInv }
  end

  hott def sigmaEqOfEq {A : Type u} {B : A → Type v} {a b : Σ x, B x}
    (p : a = b) : (Σ (p : a.1 = b.1), Equiv.subst p a.2 = b.2) :=
  begin induction p; existsi idp a.1; reflexivity end

  hott def eqOfSigmaEq {A : Type u} {B : A → Type v} {a b : Σ x, B x}
    (p : Σ (p : a.1 = b.1), Equiv.subst p a.2 = b.2) : (a = b) :=
  Sigma.prod p.1 p.2

  hott def prodRepr {A : Type u} {B : A → Type v} {a b : Σ x, B x} :
    @eqOfSigmaEq A B a b ∘ @sigmaEqOfEq A B a b ~ id :=
  begin intro p; induction p; reflexivity end

  hott def reprProd {A : Type u} {B : A → Type v} : Π {a b : Σ x, B x},
    @sigmaEqOfEq A B a b ∘ @eqOfSigmaEq A B a b ~ id :=
  begin intro ⟨a, u⟩ ⟨b, v⟩ ⟨(p : a = b), q⟩; induction p; dsimp at q; induction q; apply idp end

  hott def sigmaPath {A : Type u} {B : A → Type v} {a b : Σ x, B x} :
    (a = b) ≃ (Σ (p : a.1 = b.1), Equiv.subst p a.2 = b.2) :=
  begin
    existsi sigmaEqOfEq; apply Qinv.toBiinv;
    existsi eqOfSigmaEq; apply Prod.mk; apply reprProd; apply prodRepr
  end
end Sigma

end GroundZero.Types