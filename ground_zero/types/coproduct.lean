import ground_zero.types.equiv

namespace ground_zero.types

hott theory

universes u v f

abbreviation coproduct (α : Type u) (β : Type v) := sum α β
infix ` + ` := coproduct

namespace coproduct
  variables {α : Type u} {β : Type v}

  @[pattern] abbreviation inl : α → α + β := sum.inl
  @[pattern] abbreviation inr : β → α + β := sum.inr

  @[hott] def elim {γ : Type f} (g₀ : α → γ) (g₁ : β → γ) : α + β → γ
  | (inl a) := g₀ a
  | (inr b) := g₁ b

  @[hott] def inv : α + β → β + α
  | (coproduct.inl x) := coproduct.inr x
  | (coproduct.inr x) := coproduct.inl x

  @[hott] theorem symm : α + β ≃ β + α := begin
    existsi inv, split; existsi inv;
    { intro x, induction x; trivial }
  end

  namespace inl
    @[hott] def code (a₀ : α) : α + β → Type u
    | (inl a) := a₀ = a :> α
    | (inr b) := 𝟎

    @[hott] def encode {a₀ : α} {x : α + β} (p : inl a₀ = x) : code a₀ x :=
    equiv.transport (code a₀) p eq.rfl

    @[hott] def decode {a₀ : α} : Π {x : α + β} (c : code a₀ x), inl a₀ = x
    | (inl a) c := inl # c
    | (inr b) c := by cases c

    @[hott] def decode_encode {a₀ : α} {x : α + β}
      (p : inl a₀ = x) : decode (encode p) = p :=
    begin induction p, trivial end

    @[hott] def encode_decode {a₀ : α} {x : α + β} (c : code a₀ x) :
      encode (decode c) = c :> _ := begin
      induction x,
      { transitivity, symmetry, apply equiv.transport_comp,
        apply equiv.transport_composition },
      { cases c }
    end

    @[hott] def recognize (a₀ : α) (x : α + β) :
      (inl a₀ = x) ≃ code a₀ x := begin
      existsi encode, split; existsi decode,
      apply decode_encode, apply encode_decode
    end

    @[hott] def inj' (x y : α) : (inl x = inl y :> α + β) ≃ (x = y) :=
    recognize x (inl y)

    @[hott] def inl_inr (x : α) (y : β) : (inl x = inr y) ≃ 𝟎 :=
    recognize x (inr y)
  end inl

  namespace inr
    @[hott] def code (b₀ : β) : α + β → Type v
    | (inl a) := 𝟎
    | (inr b) := b₀ = b :> β

    @[hott] def encode {b₀ : β} {x : α + β}
      (p : inr b₀ = x :> α + β) : code b₀ x :=
    equiv.transport (code b₀) p eq.rfl

    @[hott] def decode {b₀ : β} : Π {x : α + β} (c : code b₀ x), inr b₀ = x
    | (inl a) c := by cases c
    | (inr b) c := inr # c

    @[hott] def decode_encode {b₀ : β} {x : α + β}
      (p : inr b₀ = x) : decode (encode p) = p :=
    begin induction p, trivial end

    @[hott] def encode_decode {b₀ : β} {x : α + β} (c : code b₀ x) :
      encode (decode c) = c := begin
      induction x,
      { cases c },
      { transitivity, symmetry,
        apply equiv.transport_comp,
        apply equiv.transport_composition }
    end

    @[hott] def recognize (b₀ : β) (x : α + β) :
      (inr b₀ = x :> α + β) ≃ code b₀ x := begin
      existsi encode, split; existsi decode,
      apply decode_encode, apply encode_decode
    end

    @[hott] def inj' (x y : β) : (inr x = inr y :> α + β) ≃ (x = y) :=
    recognize x (inr y)

    @[hott] def inr_inl (x : β) (y : α) : (inr x = inl y :> α + β) ≃ 𝟎 :=
    recognize x (inl y)
  end inr
end coproduct

end ground_zero.types