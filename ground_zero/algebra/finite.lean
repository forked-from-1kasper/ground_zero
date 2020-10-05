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

  @[hott] def coset {G : group} (h : G.carrier) (φ : ens G.carrier) : ens G.carrier :=
  ⟨λ x, Σ y, (y ∈ φ) × (x = G.φ h y), begin
    intros x p q, induction p with a p, induction q with b q,
    fapply types.sigma.prod, fapply mul_cancel_left, exact h,
    transitivity, exact p.snd⁻¹, exact q.snd,
    apply structures.product_prop,
    { apply ens.prop }, { apply G.set }
  end⟩

  @[hott] def coset.intro {G : group} {a b : G.carrier} {φ : ens G.carrier} :
    b ∈ φ → G.φ a b ∈ coset a φ := begin
    intro p, existsi b, split,
    assumption, reflexivity
  end

  @[hott] def coset.triv {G : group} (h : G.carrier)
    (φ : ens G.carrier) [G ≥ φ] : h ∈ coset h φ := begin
    existsi G.e, split, { apply is_subgroup.unit },
    { symmetry, apply G.mul_one }
  end

  @[hott] noncomputable def coset.idem {G : group} (φ : ens G.carrier) [G ≥ φ]
    {x : G.carrier} : x ∈ φ → coset x φ = φ := begin
    intro p, apply ens.ext, intro y, split; intro q,
    { induction q with z q, apply transport (∈ φ), exact q.snd⁻¹,
      apply is_subgroup.mul, exact p, exact q.fst },
    { existsi G.φ (G.inv x) y, split,
      { apply is_subgroup.mul,
        { apply is_subgroup.inv, exact p }, exact q },
      { transitivity, { symmetry, apply G.one_mul },
        symmetry, transitivity, { symmetry, apply G.mul_assoc },
        apply map (λ x, G.φ x y), apply mul_right_inv } }
  end

  @[hott] noncomputable def coset.assoc {G : group} {a b : G.carrier} (φ : ens G.carrier)
    [G ≥ φ] : coset a (coset b φ) = coset (G.φ a b) φ := begin
    apply ens.ext, intro x, split; intro p,
    { cases p with y p, cases p with p r, cases p with z p, cases p with p q,
      apply transport (∈ coset (G.φ a b) φ),
      symmetry, transitivity, { transitivity, exact r, apply map (G.φ a), exact q },
      symmetry, apply G.mul_assoc, apply coset.intro p },
    { cases p with y p, apply transport (∈ coset a (coset b φ)),
      symmetry, transitivity, exact p.snd, apply G.mul_assoc,
      apply coset.intro, apply coset.intro, exact p.fst }
  end

  @[hott] noncomputable def coset.uniq {G : group} {g₁ g₂ x : G.carrier} (φ : ens G.carrier)
    [G ≥ φ] : x ∈ coset g₁ φ → x ∈ coset g₂ φ → coset g₁ φ = coset g₂ φ := begin
    intros p q, induction p with x₁ p, induction q with x₂ q,
    transitivity, apply map (λ x, coset x φ), calc
       g₁ = G.φ g₁ G.e : (G.mul_one g₁)⁻¹
      ... = G.φ g₁ (G.φ x₁ (G.inv x₁)) : (G.φ g₁) # (mul_right_inv x₁)⁻¹
      ... = G.φ (G.φ g₁ x₁) (G.inv x₁) : (G.mul_assoc _ _ _)⁻¹
      ... = G.φ (G.φ g₂ x₂) (G.inv x₁) : (λ x, G.φ x (G.inv x₁)) # (p.snd⁻¹ ⬝ q.snd)
      ... = G.φ g₂ (G.φ x₂ (G.inv x₁)) : G.mul_assoc _ _ _,
    transitivity, { symmetry, apply coset.assoc },
    apply map, apply coset.idem, apply is_subgroup.mul,
    exact q.fst, apply is_subgroup.inv, exact p.fst
  end

  @[hott] def coset.all {G : group} (φ : subgroup G) : ens G.carrier :=
  ens.sunion (λ s, Σ y, s = coset y φ.fst)

  @[hott] def coset.total {G : group} (φ : subgroup G) :
    G.carrier → (coset.all φ).subtype := begin
    intro x, existsi x, apply HITs.merely.elem,
    existsi coset x φ.fst, split,
    apply coset.triv, existsi x, reflexivity
  end

  def coset.repr (G : group) (φ : subgroup G) :
    G.carrier ≃ (coset.all φ).subtype := begin
    existsi coset.total φ, split; existsi sigma.fst; intro x,
    { reflexivity },
    { induction x with x p, fapply types.sigma.prod,
      { reflexivity }, { apply ens.prop } }
  end
end group

end algebra

end ground_zero