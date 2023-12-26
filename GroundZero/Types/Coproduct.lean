import GroundZero.Types.Equiv

open GroundZero.Types.Id (ap)

namespace GroundZero.Types
universe u v w w'

hott definition Coproduct (A : Type u) (B : Type v) := Sum A B

infixl:65 " + " => Coproduct

attribute [eliminator] Sum.casesOn

namespace Coproduct
  variable {A : Type u} {B : Type v}

  @[match_pattern] hott abbreviation inl : A → A + B := Sum.inl
  @[match_pattern] hott abbreviation inr : B → A + B := Sum.inr

  hott definition elim {C : Type w} (g₀ : A → C) (g₁ : B → C) : A + B → C
  | inl a => g₀ a
  | inr b => g₁ b

  hott definition bimap {C : Type w} {C' : Type w'} (f : A → C) (g : B → C') : A + B → C + C' :=
  elim (Sum.inl ∘ f) (Sum.inr ∘ g)

  hott definition inv : A + B → B + A
  | inl x => inr x
  | inr x => inl x

  hott definition symm : A + B ≃ B + A :=
  begin
    existsi inv; apply Qinv.toBiinv; existsi inv;
    apply Prod.mk <;> { intro x; induction x using Sum.casesOn <;> reflexivity }
  end

  namespace inl
    hott definition code (a₀ : A) : A + B → Type u
    | inl a => a₀ = a
    | inr b => 𝟎

    hott definition encode {a₀ : A} {x : A + B} (p : inl a₀ = x) : code a₀ x :=
    Equiv.transport (code a₀) p (idp a₀)

    hott definition decode {a₀ : A} : Π {x : A + B} (c : code a₀ x), inl a₀ = x
    | inl a, c => ap inl c
    | inr b, c => Proto.Empty.elim c

    hott statement decodeEncode {a₀ : A} {x : A + B}
      (p : inl a₀ = x) : decode (encode p) = p :=
    begin induction p; reflexivity end

    hott lemma encodeDecode {a₀ : A} {x : A + B} : Π (c : code a₀ x), encode (decode c) = c :=
    begin
      induction x using Sum.casesOn; intro (p : a₀ = _);
      induction p; apply idp; apply Proto.Empty.casesOn
    end

    hott lemma recognize (a₀ : A) (x : A + B) : (inl a₀ = x) ≃ code a₀ x :=
    begin
      existsi encode; apply Qinv.toBiinv; existsi decode;
      apply Prod.mk; apply encodeDecode; apply decodeEncode
    end

    hott corollary inj' (x y : A) : @Id (A + B) (inl x) (inl y) ≃ (x = y) :=
    recognize x (inl y)

    hott corollary inlInr (x : A) (y : B) : @Id (A + B) (inl x) (inr y) ≃ 𝟎 :=
    recognize x (inr y)
  end inl

  namespace inr
    hott definition code (b₀ : B) : A + B → Type v
    | inl a => 𝟎
    | inr b => b₀ = b

    hott definition encode {b₀ : B} {x : A + B} (p : inr b₀ = x) : code b₀ x :=
    Equiv.transport (code b₀) p (idp b₀)

    hott definition decode {b₀ : B} : Π {x : A + B} (c : code b₀ x), inr b₀ = x
    | inl a, c => Proto.Empty.elim c
    | inr b, c => ap inr c

    hott statement decodeEncode {b₀ : B} {x : A + B}
      (p : inr b₀ = x) : decode (encode p) = p :=
    begin induction p; reflexivity end

    hott lemma encodeDecode {b₀ : B} {x : A + B} : Π (c : code b₀ x), encode (decode c) = c :=
    begin
      induction x using Sum.casesOn; apply Proto.Empty.casesOn;
      intro (p : b₀ = _); induction p; apply idp;
    end

    hott lemma recognize (b₀ : B) (x : A + B) : (inr b₀ = x) ≃ code b₀ x :=
    begin
      existsi encode; apply Qinv.toBiinv; existsi decode;
      apply Prod.mk; apply encodeDecode; apply decodeEncode
    end

    hott corollary inj' (x y : B) : @Id (A + B) (inr x) (inr y) ≃ (x = y) :=
    recognize x (inr y)

    hott corollary inrInl (x : B) (y : A) : @Id (A + B) (inr x) (inl y) ≃ 𝟎 :=
    recognize x (inl y)
  end inr

  hott definition code {A B : Type u} : A + B → A + B → Type u
  | inl a => inl.code a
  | inr b => inr.code b

  hott definition pathSum {A B : Type u} (z₁ z₂ : A + B) (p : code z₁ z₂) : z₁ = z₂ :=
  begin
    induction z₁ using Sum.casesOn <;> induction z₂ using Sum.casesOn;
    apply ap; assumption; apply Proto.Empty.elim p;
    apply Proto.Empty.elim p; apply ap; assumption
  end
end Coproduct

end GroundZero.Types
