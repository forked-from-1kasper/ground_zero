import GroundZero.Types.Equiv

namespace GroundZero.Types
universe u v w w'

def Coproduct (A : Type u) (B : Type v) := Sum A B
infixl:65 " + " => Coproduct

attribute [eliminator] Sum.casesOn

namespace Coproduct
  variable {A : Type u} {B : Type v}

  @[matchPattern] def inl : A → A + B := Sum.inl
  @[matchPattern] def inr : B → A + B := Sum.inr

  hott def elim {C : Type w} (g₀ : A → C) (g₁ : B → C) : A + B → C
  | inl a => g₀ a
  | inr b => g₁ b

  hott def bimap {C : Type w} {C' : Type w'} (f : A → C) (g : B → C') : A + B → C + C' :=
  elim (Sum.inl ∘ f) (Sum.inr ∘ g)

  hott def inv : A + B → B + A
  | inl x => inr x
  | inr x => inl x

  hott def symm : A + B ≃ B + A :=
  begin
    existsi inv; apply Qinv.toBiinv; existsi inv;
    apply Prod.mk <;> { intro x; induction x using Sum.casesOn <;> reflexivity }
  end

  namespace inl
    hott def code (a₀ : A) : A + B → Type u
    | inl a => a₀ = a
    | inr b => 𝟎

    hott def encode {a₀ : A} {x : A + B} (p : inl a₀ = x) : code a₀ x :=
    Equiv.transport (code a₀) p (idp a₀)

    hott def decode {a₀ : A} : Π {x : A + B} (c : code a₀ x), inl a₀ = x
    | inl a, c => Id.map inl c
    | inr b, c => Proto.Empty.elim c

    hott def decodeEncode {a₀ : A} {x : A + B}
      (p : inl a₀ = x) : decode (encode p) = p :=
    begin induction p; reflexivity end

    hott def encodeDecode {a₀ : A} {x : A + B} : Π (c : code a₀ x), encode (decode c) = c :=
    begin
      induction x using Sum.casesOn; intro (p : a₀ = _);
      induction p; apply idp; apply Proto.Empty.casesOn
    end

    hott def recognize (a₀ : A) (x : A + B) : (inl a₀ = x) ≃ code a₀ x :=
    begin
      existsi encode; apply Qinv.toBiinv; existsi decode;
      apply Prod.mk; apply encodeDecode; apply decodeEncode
    end

    hott def inj' (x y : A) : @Id (A + B) (inl x) (inl y) ≃ (x = y) :=
    recognize x (inl y)

    hott def inlInr (x : A) (y : B) : @Id (A + B) (inl x) (inr y) ≃ 𝟎 :=
    recognize x (inr y)
  end inl

  namespace inr
    hott def code (b₀ : B) : A + B → Type v
    | inl a => 𝟎
    | inr b => b₀ = b

    hott def encode {b₀ : B} {x : A + B} (p : inr b₀ = x) : code b₀ x :=
    Equiv.transport (code b₀) p (idp b₀)

    hott def decode {b₀ : B} : Π {x : A + B} (c : code b₀ x), inr b₀ = x
    | inl a, c => Proto.Empty.elim c
    | inr b, c => Id.map inr c

    hott def decodeEncode {b₀ : B} {x : A + B}
      (p : inr b₀ = x) : decode (encode p) = p :=
    begin induction p; reflexivity end

    hott def encodeDecode {b₀ : B} {x : A + B} : Π (c : code b₀ x), encode (decode c) = c :=
    begin
      induction x using Sum.casesOn; apply Proto.Empty.casesOn;
      intro (p : b₀ = _); induction p; apply idp;
    end

    hott def recognize (b₀ : B) (x : A + B) : (inr b₀ = x) ≃ code b₀ x :=
    begin
      existsi encode; apply Qinv.toBiinv; existsi decode;
      apply Prod.mk; apply encodeDecode; apply decodeEncode
    end

    hott def inj' (x y : B) : @Id (A + B) (inr x) (inr y) ≃ (x = y) :=
    recognize x (inr y)

    hott def inrInl (x : B) (y : A) : @Id (A + B) (inr x) (inl y) ≃ 𝟎 :=
    recognize x (inl y)
  end inr

  hott def code {A B : Type u} : A + B → A + B → Type u
  | inl a => inl.code a
  | inr b => inr.code b

  hott def pathSum {A B : Type u} (z₁ z₂ : A + B) (p : code z₁ z₂) : z₁ = z₂ :=
  begin
    induction z₁ using Sum.casesOn <;> induction z₂ using Sum.casesOn;
    apply Id.map; assumption; apply Proto.Empty.elim p;
    apply Proto.Empty.elim p; apply Id.map; assumption
  end
end Coproduct

end GroundZero.Types