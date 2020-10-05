import ground_zero.algebra.group
open ground_zero.types.equiv (transport)
open ground_zero.types.qinv (eqv)
open ground_zero.types.Id (map)
open ground_zero.types (idp)

hott theory

namespace ground_zero
universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}

namespace types.coproduct
  @[hott] def respects_equiv_left (e : α ≃ β) : γ + α ≃ γ + β := begin
    transitivity, apply types.coproduct.symm,
    transitivity, apply types.nat.equiv_addition,
    assumption, apply types.coproduct.symm
  end 

  @[hott] def eqv_variants (e : γ + α ≃ γ + β) (x : α) :
    (Σ y, e.forward (sum.inr x) = sum.inr y) +
    (Σ y, e.forward (sum.inr x) = sum.inl y) := begin
    cases e.forward (sum.inr x) with a b,
    { apply sum.inr, existsi a, trivial },
    { apply sum.inl, existsi b, trivial }
  end

  @[hott] def diff (f : β → α) : Type (max u v) :=
  Σ (x : α), Π y, ¬(x = f y)

  @[hott] def diff.inl : diff (@sum.inl α β) → β := begin
    intro x, induction x with x p, induction x with a b,
    { apply proto.empty.elim, apply p a, reflexivity }, { exact b }
  end

  @[hott] def empty.lift : proto.empty.{u} → proto.empty.{v} :=
  λ x, by cases x

  @[hott] def diff.inr : β → diff (@sum.inl α β) :=
  λ x, ⟨sum.inr x, λ y p, empty.lift.{(v + 1) 1}
    (@types.coproduct.inr.encode.{u v} α β x (sum.inl y) p)⟩

  @[hott] def ldiff : diff (@sum.inl α β) ≃ β := begin
    existsi diff.inl, split; existsi diff.inr; intro x,
    { induction x with x p, induction x with a b,
      { apply proto.empty.elim, apply p a, reflexivity },
      { fapply types.sigma.prod, { reflexivity },
        { apply structures.pi_prop,
          intro x, apply structures.not_is_prop } } },
    { reflexivity }
  end

  @[hott] def left : (α + β) + γ → α + (β + γ) := begin
    intro x, induction x with x c,
    { induction x with a b,
      { exact sum.inl a },
      { exact sum.inr (sum.inl b) } },
    { exact sum.inr (sum.inr c) }
  end

  @[hott] def right : α + (β + γ) → (α + β) + γ := begin
    intro x, induction x with a x,
    { exact sum.inl (sum.inl a) },
    { induction x with b c,
      { exact sum.inl (sum.inr b) },
      { exact sum.inr c } }
  end

  @[hott] def assoc : (α + β) + γ ≃ α + (β + γ) := begin
    existsi left, split; existsi right;
    { intro x, repeat { induction x <|> trivial } }
  end

  @[hott] def zero : 𝟎 + α → α
  | (sum.inl x) := proto.empty.elim x
  | (sum.inr x) := x

  @[hott] def empty : 𝟎 + α ≃ α := begin
    existsi zero, split; existsi sum.inr; intro x,
    { induction x, { cases x }, { reflexivity } },
    { reflexivity }
  end
end types.coproduct

namespace types.product
  @[hott] def destroy : 𝟎 × α ≃ 𝟎 := begin
    existsi prod.fst, split; existsi proto.empty.elim;
    intro x, { cases x.fst }, { cases x }
  end

  @[hott] def split : (α + β) × γ → (α × γ) + (β × γ)
  | (sum.inl a, c) := sum.inl (a, c)
  | (sum.inr b, c) := sum.inr (b, c)

  @[hott] def join : (α × γ) + (β × γ) → (α + β) × γ
  | (sum.inl (a, c)) := (sum.inl a, c)
  | (sum.inr (b, c)) := (sum.inr b, c)

  @[hott] def distrib_right : (α + β) × γ ≃ (α × γ) + (β × γ) := begin
    existsi split, split; existsi join; intro x,
    { induction x with x c, induction x; trivial },
    { induction x; cases x; trivial }
  end

  @[hott] def distrib_left : α × (β + γ) ≃ (α × β) + (α × γ) := begin
    transitivity, apply types.product.comm,
    transitivity, apply distrib_right,
    transitivity, { apply types.nat.equiv_addition, apply comm },
    apply types.coproduct.respects_equiv_left, apply comm
  end

  @[hott] def left : (α × β) × γ → α × (β × γ) :=
  λ ⟨⟨a, b⟩, c⟩, (a, (b, c))

  @[hott] def right : α × (β × γ) → (α × β) × γ :=
  λ ⟨a, ⟨b, c⟩⟩, ((a, b), c)

  @[hott] def assoc : (α × β) × γ ≃ α × (β × γ) := begin
    existsi left, split; existsi right; intro x,
    { induction x with x c, induction x with a b, trivial },
    { induction x with a x, induction x with b c, trivial }
  end
end types.product

namespace algebra

namespace finite
  @[hott] def finite.plus {n m : ℕ} : finite n + finite m ≃ finite (n + m) := begin
    induction n with n ih,
    { apply transport (λ p, 𝟎 + finite m ≃ finite p),
      { symmetry, apply theorems.nat.zero_plus_i },
      apply types.coproduct.empty },
    { apply transport (λ p, finite n.succ + finite m ≃ finite p),
      { symmetry, apply theorems.nat.succ_i_plus_j },
      transitivity, { apply types.nat.equiv_addition, apply types.coproduct.symm },
      transitivity, apply types.coproduct.assoc,
      transitivity, apply types.coproduct.symm,
      apply types.nat.equiv_addition, assumption }
  end

  @[hott] def finite.mul {n m : ℕ} : finite n × finite m ≃ finite (n * m) := begin
    induction n with n ih,
    { apply transport (λ p, 𝟎 × finite m ≃ finite p),
      { symmetry, apply theorems.nat.zero_mul_n },
      apply types.product.destroy },
    { apply transport (λ p, finite n.succ × finite m ≃ finite p),
      { symmetry, apply theorems.nat.mul_succ_i_j },
      transitivity, apply types.product.distrib_right,
      transitivity, { apply types.coproduct.respects_equiv_left,
                      apply structures.prod_unit_equiv },
      transitivity, { apply types.nat.equiv_addition, apply ih },
      apply finite.plus }
  end
end finite

namespace group
  class fin (G : group) :=
  (eqv : Σ n, G.carrier ≃ finite n)

  def ord (G : group) [fin G] := (@fin.eqv G _).fst
end group

end algebra

end ground_zero