import ground_zero.HITs.interval ground_zero.HITs.truncation ground_zero.types.sigma
open ground_zero.HITs.interval
open ground_zero.structures (prop contr hset prop_is_set)
open ground_zero.types.equiv
open ground_zero.types

namespace ground_zero
namespace theorems.prop

hott theory

universes u v w

@[hott] def product_prop {α : Type u} {β : Type v}
  (h : prop α) (g : prop β) : prop (α × β) := begin
  intros a b,
  cases a with x y, cases b with u v,
  have p := h x u, have q := g y v,
  induction p, induction q, reflexivity
end

@[hott] def contr_equiv_unit {α : Type u} (h : contr α) : α ≃ types.unit := begin
  existsi (λ _, types.unit.star), split;
  existsi (λ _, h.point),
  { intro x, apply h.intro },
  { intro x, cases x, reflexivity }
end

@[hott] lemma uniq_does_not_add_new_paths {α : Type u} (a b : ∥α∥) (p : a = b :> ∥α∥) :
  HITs.truncation.uniq a b = p :> a = b :> ∥α∥ :=
prop_is_set HITs.truncation.uniq (HITs.truncation.uniq a b) p

@[hott] lemma prop_is_prop {α : Type u} : prop (prop α) := begin
  intros f g,
  have p := λ a b, (prop_is_set f) (f a b) (g a b),
  apply theorems.dfunext, intro a,
  apply theorems.dfunext, intro b,
  exact p a b
end

@[hott] def prop_equiv {π : Type u} (h : prop π) : π ≃ ∥π∥ := begin
  existsi HITs.truncation.elem,
  split; existsi (HITs.truncation.rec h id); intro x,
  { reflexivity },
  { apply HITs.truncation.uniq }
end

@[hott] def prop_from_equiv {π : Type u} (e : π ≃ ∥π∥) : prop π := begin
  cases e with f H, cases H with linv rinv,
  cases linv with g α, cases rinv with h β,
  intros a b,
  transitivity, exact (α a)⁻¹,
  symmetry, transitivity, exact (α b)⁻¹,
  apply eq.map g, exact HITs.truncation.uniq (f b) (f a)
end

@[hott] def map_to_happly {α : Type u} {β : Type v}
  (c : α) (f g : α → β) (p : f = g) :
  (λ (f : α → β), f c) # p = theorems.happly p c :=
begin induction p, trivial end

@[hott] noncomputable def biinv_prop {α : Type u} {β : Type v}
  (f : α → β) : prop (types.equiv.biinv f) := begin
  intros m n, cases m with linv₁ rinv₁, cases n with linv₂ rinv₂,
  cases rinv₁ with g G, cases rinv₂ with h H,
  cases linv₁ with g' G', cases linv₂ with h' H',
  { apply prod.eq,
    { fapply types.sigma.prod,
      { apply theorems.funext, intro x,
        transitivity, symmetry, apply H',
        apply types.eq.map h',
        apply types.qinv.rinv_inv f g g' G G' },
      { apply theorems.dfunext, intro x,
        transitivity, apply HITs.interval.transport_over_hmtpy,
        transitivity, apply equiv.transport_over_function,
        transitivity, apply eq.map (⬝ G' x),
        transitivity, apply eq.map_inv, apply eq.map,
        apply map_to_happly,
        transitivity, apply eq.map (⬝ G' x), apply eq.map,
        apply theorems.happly, apply HITs.interval.happly_funext,
        transitivity, apply eq.map (⬝ G' x),
        apply types.eq.explode_inv,
        transitivity, apply eq.map (⬝ G' x),
        apply eq.map, apply eq.inv_inv,
        transitivity, apply eq.map, apply eq.map (⬝ H' (g' (f x))),
        transitivity, symmetry, apply eq.map_inv,
        apply eq.map, apply types.eq.explode_inv,
        transitivity, apply eq.map (⬝ G' x),
        apply eq.map (⬝ H' (g' (f x))),
        apply types.equiv.map_functoriality,
        admit } },
    { fapply types.sigma.prod,
      { apply theorems.funext, intro x,
        transitivity, symmetry, apply types.eq.map, apply H,
        apply types.qinv.linv_inv f g g' G G' },
      { apply theorems.dfunext, intro x, admit } } },
end

@[hott] noncomputable theorem prop_exercise (π : Type u) : (prop π) ≃ (π ≃ ∥π∥) :=
begin
  existsi @prop_equiv π, split; existsi prop_from_equiv,
  { intro x, apply prop_is_prop },
  { intro x,
    induction x with f H,
    induction H with linv rinv,
    induction linv with f α,
    induction rinv with g β,
    fapply sigma.prod,
    { apply theorems.funext, intro x, apply HITs.truncation.uniq },
    { apply biinv_prop } }
end

@[hott] lemma comp_qinv₁ {α : Type u} {β : Type v} {γ : Type w}
  (f : α → β) (g : β → α) (H : is_qinv f g) :
  @qinv (γ → α) (γ → β) (λ (h : γ → α), f ∘ h) := begin
  existsi (λ h, g ∘ h), split;
  intro h; apply theorems.funext; intro x,
  apply H.pr₁, apply H.pr₂
end

@[hott] lemma comp_qinv₂ {α : Type u} {β : Type v} {γ : Type w}
  (f : α → β) (g : β → α) (H : is_qinv f g) :
  @qinv (β → γ) (α → γ) (λ (h : β → γ), h ∘ f) := begin
  existsi (λ h, h ∘ g), split;
  intro h; apply theorems.funext; intro x; apply eq.map h,
  apply H.pr₂, apply H.pr₁
end

@[hott] def lem_contr_inv {α : Type u} (h : prop α) (x : α) : contr α := ⟨x, h x⟩

@[hott] def lem_contr_equiv {α : Type u} : (prop α) ≃ (α → contr α) := begin
  apply structures.prop_equiv_lemma,
  { apply structures.prop_is_prop },
  { apply structures.function_to_contr },
  apply lem_contr_inv, apply structures.lem_contr
end

@[hott] def contr_to_type {α : Type u} {β : α → Type v}
  (h : contr α) : (Σ x, β x) → β h.point
| ⟨x, u⟩ := types.equiv.subst (h.intro x)⁻¹ u

@[hott] def type_to_contr {α : Type u} {β : α → Type v}
  (h : contr α) : β h.point → (Σ x, β x) :=
λ u, ⟨h.point, u⟩

-- HoTT 3.20
@[hott] def contr_family {α : Type u} {β : α → Type v} (h : contr α) :
  (Σ x, β x) ≃ β h.point := begin
  existsi contr_to_type h, split;
  existsi @type_to_contr α β h; intro x,
  { cases x with x u, fapply types.sigma.prod,
    { apply h.intro },
    { apply types.equiv.transport_back_and_forward } },
  { transitivity, apply eq.map (λ p, types.equiv.subst p x),
    apply prop_is_set (structures.contr_impl_prop h) _ eq.rfl,
    trivial }
end

end theorems.prop
end ground_zero