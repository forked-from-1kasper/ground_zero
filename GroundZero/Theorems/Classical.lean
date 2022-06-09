import GroundZero.Theorems.Equiv
open GroundZero.Types.Equiv (transport)
open GroundZero.Types.Id (map)
open GroundZero.Structures
open GroundZero.Types

namespace GroundZero
universe u v w

namespace Theorems.Classical

axiom choice {A : Type u} (B : A → Type v) (η : Π x, B x → Type w) :
  hset A → (Π x, hset (B x)) → (Π x y, prop (η x y)) →
  (Π (x : A), ∥(Σ (y : B x), η x y)∥) →
  ∥(Σ (φ : Π x, B x), Π x, η x (φ x))∥

noncomputable hott def choiceOfRel {A : Type u} {B : Type v}
  (R : A → B → propset.{w}) (H : hset A) (G : hset B) :
  (Π x, ∥(Σ y, (R x y).fst)∥) → ∥(Σ (φ : A → B), Π x, (R x (φ x)).fst)∥ :=
begin
  apply @choice A (λ _, B) (λ x y, (R x y).1);
  { intros x y; apply H };
  { intros x y z; apply G };
  { intros x y; apply (R x y).2 }
end

noncomputable hott def cartesian {A : Type u} (B : A → Type v) :
  hset A → (Π x, hset (B x)) → (Π x, ∥B x∥) → ∥(Π x, B x)∥ :=
begin
  intros p q φ; apply transport; apply GroundZero.ua;
  change (Σ (φ : Π x, B x), Π (x : A), (𝟏 : Type)) ≃ _;
  transitivity; apply Sigma.const; apply Equiv.trans;
  { apply GroundZero.ua.productEquiv₃;
    { reflexivity }; { apply zeroMorphismEqv.{_, _, 1} } };
  apply Equiv.trans; apply Product.comm; apply prodUnitEquiv;
  apply choice B (λ _ _, 𝟏); apply p; apply q;
  { intros; apply unitIsProp }; intro x; fapply HITs.Merely.rec _ _ (φ x);
  apply HITs.Merely.uniq; intro y; apply HITs.Merely.elem; exact ⟨y, ★⟩
end

hott def propExcludedMiddle {A : Type u} (H : prop A) : prop (A + ¬A) :=
begin
  intros x y; match x, y with
  | Sum.inl _, Sum.inl _ => _
  | Sum.inr x, Sum.inl y => _
  | Sum.inl x, Sum.inr y => _
  | Sum.inr _, Sum.inr _ => _;
  { apply map; apply H };
  { apply Proto.Empty.elim; apply x y };
  { apply Proto.Empty.elim; apply y x };
  { apply map; apply notIsProp }
end

section
  variable {A : Type u} (H : prop A)
  def inh := Σ (φ : 𝟐 → Ω), ∥(Σ (x : 𝟐), (φ x).fst)∥

  noncomputable hott def inh.hset : hset inh :=
  begin
    apply hsetRespectsSigma; apply piHset;
    intro x; apply Theorems.Equiv.propsetIsSet;
    intro φ; apply propIsSet; apply HITs.Merely.uniq
  end

  -- due to http://www.cs.ioc.ee/ewscs/2017/altenkirch/altenkirch-notes.pdf
  noncomputable hott def lem {A : Type u} (H : prop A) : A + ¬A :=
  begin
    have f := @choiceOfRel inh 𝟐 (λ φ x, φ.fst x) inh.hset boolIsSet (λ x, HITs.Merely.lift id x.2);
    induction f; case elemπ w =>
    { let ⟨φ, p⟩ := w;
      let U : 𝟐 → Ω := λ x, ⟨∥(x = true) + A∥,  HITs.Merely.uniq⟩;
      let V : 𝟐 → Ω := λ x, ⟨∥(x = false) + A∥, HITs.Merely.uniq⟩;
      have r : ∥_∥ := p ⟨U, HITs.Merely.elem ⟨true,  HITs.Merely.elem (Sum.inl (idp _))⟩⟩;
      have s : ∥_∥ := p ⟨V, HITs.Merely.elem ⟨false, HITs.Merely.elem (Sum.inl (idp _))⟩⟩;
      induction r; case elemπ r' =>
      { induction s; case elemπ s' =>
        { induction r' using Sum.casesOn;
          case inl r' =>
          { induction s' using Sum.casesOn;
            case inl s' =>
            { right; intro z; apply ffNeqTt;
              transitivity; exact s'⁻¹; symmetry; transitivity; exact r'⁻¹;
              apply map; fapply Types.Sigma.prod; apply Theorems.funext;
              intro x; apply Theorems.Equiv.propset.Id; apply GroundZero.ua.propext;
              apply HITs.Merely.uniq; apply HITs.Merely.uniq; apply Prod.mk <;>
              intro <;> apply HITs.Merely.elem <;> right <;> exact z; apply HITs.Merely.uniq };
            case inr => { left; assumption } };
          case inr => { left; assumption } };
        apply propExcludedMiddle H };
      apply propExcludedMiddle H };
    apply propExcludedMiddle H
  end
end

noncomputable hott def dneg.decode {A : Type u} (H : prop A) : ¬¬A → A :=
λ G, match lem H with
| Sum.inl z => z
| Sum.inr φ => Proto.Empty.elim (G φ)

hott def dneg.encode {A : Type u} : A → ¬¬A :=
λ x p, p x

noncomputable hott def dneg {A : Type u} (H : prop A) : A ≃ ¬¬A :=
propEquivLemma H notIsProp dneg.encode (dneg.decode H)

section
  variable {A : Type u} {B : Type v} (H : prop B)

  hott def Contrapos.intro : (A → B) → (¬B → ¬A) :=
  λ f p a, p (f a)

  noncomputable hott def Contrapos.elim : (¬B → ¬A) → (A → B) :=
  λ f p, match lem H with
  | Sum.inl z => z
  | Sum.inr φ => Proto.Empty.elim (f φ p)

  noncomputable hott def Contrapos : (A → B) ↔ (¬B → ¬A) :=
  ⟨Contrapos.intro, Contrapos.elim H⟩

  noncomputable hott def Contrapos.eq (H : prop B) : (A → B) = (¬B → ¬A) :=
  begin
    apply GroundZero.ua; apply propEquivLemma;
    apply piProp; intro; assumption;
    apply piProp; intro; apply notIsProp;
    apply Contrapos.intro; apply Contrapos.elim H
  end
end
end Theorems.Classical

end GroundZero