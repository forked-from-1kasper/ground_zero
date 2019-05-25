import ground_zero.types.equiv

namespace ground_zero.types

universes u v f

inductive coproduct (α : Sort u) (β : Sort v)
| inl {} : α → coproduct
| inr {} : β → coproduct
infix ` + ` := coproduct

namespace coproduct
  variables {α : Sort u} {β : Sort v}

  def elim {γ : Sort f} (g₀ : α → γ) (g₁ : β → γ) : α + β → γ
  | (inl a) := g₀ a
  | (inr b) := g₁ b

  def inv : α + β → β + α
  | (coproduct.inl x) := coproduct.inr x
  | (coproduct.inr x) := coproduct.inl x

  theorem symm : α + β ≃ β + α := begin
    existsi inv, split; existsi inv;
    { intro x, induction x; trivial }
  end

  namespace inl
    def code (a₀ : α) : α + β → Sort u
    | (inl a) := a₀ = a :> α
    | (inr b) := 𝟎

    def encode {a₀ : α} {x : α + β} (p : inl a₀ = x :> _) : code a₀ x :=
    equiv.transport (code a₀) p eq.rfl

    def decode {a₀ : α} : Π {x : α + β} (c : code a₀ x), inl a₀ = x :> _
    | (inl a) c := inl # c
    | (inr b) c := by cases c

    def decode_encode {a₀ : α} {x : α + β}
      (p : inl a₀ = x :> _) : decode (encode p) = p :> _ :=
    begin induction p, trivial end

    def encode_decode {a₀ : α} {x : α + β} (c : code a₀ x) :
      encode (decode c) = c :> _ := begin
      induction x,
      { transitivity, symmetry, apply equiv.transport_comp,
        apply equiv.transport_composition },
      { cases c }
    end

    def recognize (a₀ : α) (x : α + β) : (inl a₀ = x :> _) ≃ code a₀ x := begin
      existsi encode, split; existsi decode,
      apply decode_encode, apply encode_decode
    end

    def inj' (x y : α) : (inl x = inl y :> α + β) ≃ (x = y :> α) :=
    recognize x (inl y)

    def inl_inr (x : α) (y : β) : (inl x = inr y :> α + β) ≃ 𝟎 :=
    recognize x (inr y)
  end inl

  namespace inr
    def code (b₀ : β) : α + β → Sort v
    | (inl a) := 𝟎
    | (inr b) := b₀ = b :> β

    def encode {b₀ : β} {x : α + β} (p : inr b₀ = x :> _) : code b₀ x :=
    equiv.transport (code b₀) p eq.rfl

    def decode {b₀ : β} : Π {x : α + β} (c : code b₀ x), inr b₀ = x :> _
    | (inl a) c := by cases c
    | (inr b) c := inr # c

    def decode_encode {b₀ : β} {x : α + β}
      (p : inr b₀ = x :> _) : decode (encode p) = p :> _ :=
    begin induction p, trivial end

    def encode_decode {b₀ : β} {x : α + β} (c : code b₀ x) :
      encode (decode c) = c :> _ := begin
      induction x,
      { cases c },
      { transitivity, symmetry, apply equiv.transport_comp,
        apply equiv.transport_composition }
    end

    def recognize (b₀ : β) (x : α + β) : (inr b₀ = x :> _) ≃ code b₀ x := begin
      existsi encode, split; existsi decode,
      apply decode_encode, apply encode_decode
    end

    def inj' (x y : β) : (inr x = inr y :> α + β) ≃ (x = y :> β) :=
    recognize x (inr y)

    def inr_inl (x : β) (y : α) : (inr x = inl y :> α + β) ≃ 𝟎 :=
    recognize x (inl y)
  end inr
end coproduct

end ground_zero.types