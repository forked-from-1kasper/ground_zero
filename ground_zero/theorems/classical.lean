import ground_zero.theorems.ua
import ground_zero.theorems.prop
open ground_zero.types.equiv (transport)
open ground_zero.types.Id (map)
open ground_zero.structures
open ground_zero.types

namespace ground_zero
universes u v w

hott theory

namespace theorems.classical

axiom choice {α : Type u} (β : α → Type v) (η : Π x, β x → Type w) :
  hset α → (Π x, hset (β x)) → (Π x y, prop (η x y)) →
  (Π (x : α), ∥(Σ (y : β x), η x y)∥) →
  ∥(Σ (φ : Π x, β x), Π x, η x (φ x))∥

@[hott] noncomputable def choice_of_rel {α : Type u} {β : Type v}
  (R : α → β → propset.{w}) (H : hset α) (G : hset β) :
  (Π x, ∥(Σ y, (R x y).fst)∥) → ∥(Σ (φ : α → β), Π x, (R x (φ x)).fst)∥ := begin
  apply @choice α (λ _, β) (λ x y, (R x y).fst),
  { intros x y, apply H },
  { intros x y z, apply G },
  { intros x y, apply (R x y).snd }
end

@[hott] noncomputable def cartesian {α : Type u} (β : α → Type v) :
  hset α → (Π x, hset (β x)) → (Π x, ∥β x∥) → ∥(Π x, β x)∥ :=
begin
  intros p q φ, apply transport, apply ground_zero.ua,
  change (Σ (φ : Π x, β x), Π (x : α), (𝟏 : Type)) ≃ _,
  transitivity, apply types.sigma.const, transitivity,
  { apply ground_zero.ua.product_equiv₃,
    { reflexivity }, { apply zero_morphism_eqv } },
  transitivity, apply product.comm, apply prod_unit_equiv,
  apply choice β (λ _ _, 𝟏), { intros x y, apply p }, exact q,
  { intros x h, apply unit_is_prop }, intro x, fapply HITs.merely.rec _ _ (φ x),
  apply HITs.merely.uniq, intro y, apply HITs.merely.elem, exact ⟨y, ★⟩
end

@[hott] def prop_excluded_middle {α : Type u} (H : prop α) : prop (α + ¬α) :=
begin
  intros x y, induction x; induction y,
  { apply map, apply H },
  { apply proto.empty.elim, apply y x },
  { apply proto.empty.elim, apply x y },
  { apply map, apply not_is_prop }
end

section
  variables {α : Type u} (H : prop α)
  def inh := Σ (φ : 𝟐 → propset), ∥(Σ (x : 𝟐), (φ x).fst)∥

  @[hott] noncomputable def prop_eq_prop {α β : Type u} (G : prop β) : prop (α = β) :=
  begin
    apply structures.prop_respects_equiv,
    apply ground_zero.ua.univalence α β,
    apply theorems.prop.prop_equiv_prop G
  end

  @[hott] noncomputable def propset.set : hset propset :=
  begin
    intros x y, induction x with x H, induction y with y G,
    apply transport (λ π, Π (p q : π), p = q),
    symmetry, apply ground_zero.ua, apply types.sigma.sigma_path,
    intros p q, induction p with p p', induction q with q q',
    change x = y at p, change x = y at q, fapply types.sigma.prod,
    { apply prop_eq_prop, exact G },
    { apply prop_is_set, apply prop_is_prop }
  end

  @[hott] noncomputable def inh.hset : hset inh :=
  begin
    apply hset_respects_sigma,
    apply pi_hset, intro x, apply propset.set,
    intro φ, apply prop_is_set, apply HITs.merely.uniq
  end

  -- due to http://www.cs.ioc.ee/ewscs/2017/altenkirch/altenkirch-notes.pdf
  @[hott] noncomputable def lem {α : Type u} (H : prop α) : α + ¬α :=
  begin
    have f := @choice_of_rel inh 𝟐 (λ φ x, φ.fst x)
      (by apply inh.hset) (by apply bool_is_set)
      (begin intro x, apply HITs.merely.lift id x.snd end),
    fapply HITs.merely.rec _ _ f,
    { apply prop_excluded_middle H },
    { intro p, induction p with φ p,
      let U : 𝟐 → propset := λ x, ⟨∥(x = tt) + α∥, HITs.merely.uniq⟩,
      let V : 𝟐 → propset := λ x, ⟨∥(x = ff) + α∥, HITs.merely.uniq⟩,
      have r := p ⟨U, HITs.merely.elem ⟨tt, HITs.merely.elem (sum.inl (idp tt))⟩⟩,
      have s := p ⟨V, HITs.merely.elem ⟨ff, HITs.merely.elem (sum.inl (idp ff))⟩⟩,
      fapply HITs.merely.rec _ _ r, apply prop_excluded_middle H,
      intro r', fapply HITs.merely.rec _ _ s, apply prop_excluded_middle H,
      intro s', induction r'; induction s',
      { right, intro z, apply ff_neq_tt,
        transitivity, exact s'⁻¹, symmetry, transitivity, exact r'⁻¹,
        apply map, fapply types.sigma.prod, apply theorems.funext,
        intro x, apply theorems.prop.propset.Id, apply ground_zero.ua.propext,
        repeat { apply HITs.merely.uniq }, split,
        repeat { intro x, apply HITs.merely.elem, right, exact z } },
      repeat { left, assumption } }
  end
end

@[hott] noncomputable def dneg.decode {α : Type u}
  (H : prop α) : ¬¬α → α :=
begin intro p, cases lem H with u v, exact u, cases p v end

@[hott] def dneg.encode {α : Type u} : α → ¬¬α :=
λ x p, p x

@[hott] noncomputable def dneg {α : Type u} (H : prop α) : α ≃ ¬¬α :=
prop_equiv_lemma H not_is_prop dneg.encode (dneg.decode H)

end theorems.classical

end ground_zero