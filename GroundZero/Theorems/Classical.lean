import GroundZero.Theorems.Prop
open GroundZero.Types.Equiv (transport)
open GroundZero.Types.Id (map)
open GroundZero.Structures
open GroundZero.Types

namespace GroundZero
universe u v w

namespace Theorems.Classical

axiom choice {α : Type u} (β : α → Type v) (η : Π x, β x → Type w) :
  hset α → (Π x, hset (β x)) → (Π x y, prop (η x y)) →
  (Π (x : α), ∥(Σ (y : β x), η x y)∥) →
  ∥(Σ (φ : Π x, β x), Π x, η x (φ x))∥

noncomputable hott def choiceOfRel {α : Type u} {β : Type v}
  (R : α → β → propset.{w}) (H : hset α) (G : hset β) :
  (Π x, ∥(Σ y, (R x y).fst)∥) → ∥(Σ (φ : α → β), Π x, (R x (φ x)).fst)∥ :=
begin
  apply @choice α (λ _, β) (λ x y, (R x y).1);
  { intros x y; apply H };
  { intros x y z; apply G };
  { intros x y; apply (R x y).2 }
end

noncomputable hott def cartesian {α : Type u} (β : α → Type v) :
  hset α → (Π x, hset (β x)) → (Π x, ∥β x∥) → ∥(Π x, β x)∥ :=
begin
  intros p q φ; apply transport; apply GroundZero.ua;
  change (Σ (φ : Π x, β x), Π (x : α), (𝟏 : Type)) ≃ _;
  transitivity; apply Sigma.const; apply Equiv.trans;
  { apply GroundZero.ua.productEquiv₃;
    { reflexivity }; { apply zeroMorphismEqv } };
  apply Equiv.trans; apply Product.comm; apply prodUnitEquiv;
  apply choice β (λ _ _, 𝟏); apply p; apply q;
  { intros; apply unitIsProp }; intro x; fapply HITs.Merely.rec _ _ (φ x);
  apply HITs.Merely.uniq; intro y; apply HITs.Merely.elem; exact ⟨y, ★⟩
end

hott def propExcludedMiddle {α : Type u} (H : prop α) : prop (α + ¬α) :=
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
  variable {α : Type u} (H : prop α)
  def inh := Σ (φ : 𝟐 → Ω), ∥(Σ (x : 𝟐), (φ x).fst)∥

  noncomputable hott def inh.hset : hset inh :=
  begin
    apply hsetRespectsSigma; apply piHset;
    intro x; apply Theorems.Prop.propsetIsSet;
    intro φ; apply propIsSet; apply HITs.Merely.uniq
  end

  -- due to http://www.cs.ioc.ee/ewscs/2017/altenkirch/altenkirch-notes.pdf
  noncomputable hott def lem {α : Type u} (H : prop α) : α + ¬α :=
  begin
    have f := @choiceOfRel inh 𝟐 (λ φ x, φ.fst x) inh.hset boolIsSet (λ x, HITs.Merely.lift id x.2);
    induction f; case elemπ w =>
    { let ⟨φ, p⟩ := w;
      let U : 𝟐 → Ω := λ x, ⟨∥(x = true) + α∥,  HITs.Merely.uniq⟩;
      let V : 𝟐 → Ω := λ x, ⟨∥(x = false) + α∥, HITs.Merely.uniq⟩;
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
              intro x; apply Theorems.Prop.propset.Id; apply GroundZero.ua.propext;
              apply HITs.Merely.uniq; apply HITs.Merely.uniq; apply Prod.mk <;>
              intro <;> apply HITs.Merely.elem <;> right <;> exact z; apply HITs.Merely.uniq };
            case inr => { left; assumption } };
          case inr => { left; assumption } };
        apply propExcludedMiddle H };
      apply propExcludedMiddle H };
    apply propExcludedMiddle H
  end
end

noncomputable hott def dneg.decode {α : Type u} (H : prop α) : ¬¬α → α :=
λ G, match lem H with
| Sum.inl z => z
| Sum.inr φ => Proto.Empty.elim (G φ)

hott def dneg.encode {α : Type u} : α → ¬¬α :=
λ x p, p x

noncomputable hott def dneg {α : Type u} (H : prop α) : α ≃ ¬¬α :=
propEquivLemma H notIsProp dneg.encode (dneg.decode H)

section
  variable {α : Type u} {β : Type v} (H : prop β)

  hott def Contrapos.intro : (α → β) → (¬β → ¬α) :=
  λ f p a, p (f a)

  noncomputable hott def Contrapos.elim : (¬β → ¬α) → (α → β) :=
  λ f p, match lem H with
  | Sum.inl z => z
  | Sum.inr φ => Proto.Empty.elim (f φ p)

  noncomputable hott def Contrapos : (α → β) ↔ (¬β → ¬α) :=
  ⟨Contrapos.intro, Contrapos.elim H⟩

  noncomputable hott def Contrapos.eq (H : prop β) : (α → β) = (¬β → ¬α) :=
  begin
    apply GroundZero.ua; apply propEquivLemma;
    apply piProp; intro; assumption;
    apply piProp; intro; apply notIsProp;
    apply Contrapos.intro; apply Contrapos.elim H
  end
end
end Theorems.Classical

end GroundZero