import GroundZero.Types.Equiv

namespace GroundZero.Types
universe u v w

def Coproduct (α : Type u) (β : Type v) := Sum α β
infixl:65 " + " => Coproduct

attribute [eliminator] Sum.casesOn

namespace Coproduct
  variable {α : Type u} {β : Type v}

  @[matchPattern] def inl : α → α + β := Sum.inl
  @[matchPattern] def inr : β → α + β := Sum.inr

  hott def elim {γ : Type w} (g₀ : α → γ) (g₁ : β → γ) : α + β → γ
  | inl a => g₀ a
  | inr b => g₁ b

  hott def inv : α + β → β + α
  | inl x => inr x
  | inr x => inl x

  hott def symm : α + β ≃ β + α :=
  begin
    existsi inv; apply Qinv.toBiinv; existsi inv;
    apply Prod.mk <;> { intro x; induction x using Sum.casesOn <;> reflexivity }
  end

  namespace inl
    hott def code (a₀ : α) : α + β → Type u
    | inl a => a₀ = a
    | inr b => 𝟎

    hott def encode {a₀ : α} {x : α + β} (p : inl a₀ = x) : code a₀ x :=
    Equiv.transport (code a₀) p (idp a₀)

    hott def decode {a₀ : α} : Π {x : α + β} (c : code a₀ x), inl a₀ = x
    | inl a, c => Id.map inl c
    | inr b, c => Proto.Empty.elim c

    hott def decodeEncode {a₀ : α} {x : α + β}
      (p : inl a₀ = x) : decode (encode p) = p :=
    begin induction p; reflexivity end

    hott def encodeDecode {a₀ : α} {x : α + β} : Π (c : code a₀ x), encode (decode c) = c :=
    begin
      induction x using Sum.casesOn; intro (p : a₀ = _);
      induction p; apply idp; apply Proto.Empty.casesOn
    end

    hott def recognize (a₀ : α) (x : α + β) : (inl a₀ = x) ≃ code a₀ x :=
    begin
      existsi encode; apply Qinv.toBiinv; existsi decode;
      apply Prod.mk; apply encodeDecode; apply decodeEncode
    end

    hott def inj' (x y : α) : @Id (α + β) (inl x) (inl y) ≃ (x = y) :=
    recognize x (inl y)

    hott def inlInr (x : α) (y : β) : @Id (α + β) (inl x) (inr y) ≃ 𝟎 :=
    recognize x (inr y)
  end inl

  namespace inr
    hott def code (b₀ : β) : α + β → Type v
    | inl a => 𝟎
    | inr b => b₀ = b

    hott def encode {b₀ : β} {x : α + β} (p : inr b₀ = x) : code b₀ x :=
    Equiv.transport (code b₀) p (idp b₀)

    hott def decode {b₀ : β} : Π {x : α + β} (c : code b₀ x), inr b₀ = x
    | inl a, c => Proto.Empty.elim c
    | inr b, c => Id.map inr c

    hott def decodeEncode {b₀ : β} {x : α + β}
      (p : inr b₀ = x) : decode (encode p) = p :=
    begin induction p; reflexivity end

    hott def encodeDecode {b₀ : β} {x : α + β} : Π (c : code b₀ x), encode (decode c) = c :=
    begin
      induction x using Sum.casesOn; apply Proto.Empty.casesOn;
      intro (p : b₀ = _); induction p; apply idp;
    end

    hott def recognize (b₀ : β) (x : α + β) : (inr b₀ = x) ≃ code b₀ x :=
    begin
      existsi encode; apply Qinv.toBiinv; existsi decode;
      apply Prod.mk; apply encodeDecode; apply decodeEncode
    end

    hott def inj' (x y : β) : @Id (α + β) (inr x) (inr y) ≃ (x = y) :=
    recognize x (inr y)

    hott def inrInl (x : β) (y : α) : @Id (α + β) (inr x) (inl y) ≃ 𝟎 :=
    recognize x (inl y)
  end inr

  hott def code {α β : Type u} : α + β → α + β → Type u
  | inl a => inl.code a
  | inr b => inr.code b

  hott def pathSum {α β : Type u} (z₁ z₂ : α + β) (p : code z₁ z₂) : z₁ = z₂ :=
  begin
    induction z₁ using Sum.casesOn <;> induction z₂ using Sum.casesOn;
    apply Id.map; assumption; apply Proto.Empty.elim p;
    apply Proto.Empty.elim p; apply Id.map; assumption
  end
end Coproduct

end GroundZero.Types