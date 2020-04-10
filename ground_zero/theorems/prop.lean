import ground_zero.HITs.interval ground_zero.HITs.merely
import ground_zero.types.product
open ground_zero.HITs.interval
open ground_zero.structures (prop contr hset prop_is_set)
open ground_zero.types.equiv
open ground_zero.types

namespace ground_zero
namespace theorems.prop

hott theory

universes u v w

@[hott] lemma uniq_does_not_add_new_paths {α : Type u} (a b : ∥α∥) (p : a = b) :
  HITs.merely.uniq a b = p :=
prop_is_set HITs.merely.uniq (HITs.merely.uniq a b) p

@[hott] def prop_equiv {π : Type u} (h : prop π) : π ≃ ∥π∥ := begin
  existsi HITs.merely.elem,
  split; existsi (HITs.merely.rec h id); intro x,
  { reflexivity },
  { apply HITs.merely.uniq }
end

@[hott] def prop_from_equiv {π : Type u} (e : π ≃ ∥π∥) : prop π := begin
  cases e with f H, cases H with linv rinv,
  cases linv with g α, cases rinv with h β,
  intros a b,
  transitivity, exact (α a)⁻¹,
  symmetry, transitivity, exact (α b)⁻¹,
  apply eq.map g, exact HITs.merely.uniq (f b) (f a)
end

@[hott] def map_to_happly {α : Type u} {β : Type v}
  (c : α) (f g : α → β) (p : f = g) :
  (λ (f : α → β), f c) # p = happly p c :=
begin induction p, trivial end

@[hott] def hmtpy_rewrite {α : Type u} (f : α → α) (H : f ~ proto.idfun) :
  Π x, H (f x) = f # (H x) := begin
  intro x,
  symmetry, transitivity, { symmetry, apply eq.refl_right }, transitivity,
  { apply eq.map (λ p, f # (H x) ⬝ p), symmetry, apply eq.comp_inv (H x) },
  transitivity, { apply eq.assoc },
  transitivity, { apply eq.map (⬝ (H x)⁻¹), symmetry, apply equiv.homotopy_square },
  transitivity, { symmetry, apply eq.assoc },
  transitivity, { apply eq.map (λ p, H (f x) ⬝ (p ⬝ (H x)⁻¹)), apply equiv.idmap },
  transitivity, { apply eq.map (λ p, H (f x) ⬝ p), apply eq.comp_inv },
  apply eq.refl_right
end

@[hott] def qinv_impls_ishae {α : Type u} {β : Type v}
  (f : α → β) : qinv f → ishae f := begin
  intro H, cases H with g H, cases H with ε η,
  let ε' := λ b, (ε (f (g b)))⁻¹ ⬝ (@eq.map α β _ _ f (η (g b)) ⬝ ε b),
  existsi g, existsi η, existsi ε', intro x,
  symmetry, transitivity,
  { apply eq.map (λ p, (ε (f (g (f x))))⁻¹ ⬝ ((@eq.map α β _ _ f p) ⬝ ε (f x))),
    apply hmtpy_rewrite (g ∘ f) },
  apply types.equiv.rewrite_comp, transitivity,
  { apply eq.map (⬝ ε (f x)), symmetry,
    apply equiv.map_over_comp (g ∘ f) },
  symmetry, apply @equiv.homotopy_square α β (f ∘ g ∘ f) f
                    (λ x, ε (f x)) (g (f x)) x (η x)
end

@[hott] def fib_eq {α : Type u} {β : Type v} (f : α → β) {y : β}
  {a b : α} (p : f a = y) (q : f b = y) (H : Σ (γ : a = b), f # γ ⬝ q = p) :
  ⟨a, p⟩ = ⟨b, q⟩ :> fib f y := begin
  induction H with γ r, fapply sigma.prod, exact γ,
  transitivity, { apply types.equiv.transport_over_contr_map },
  transitivity, { apply eq.map (⬝ p), apply types.eq.map_inv },
  apply equiv.rewrite_comp, exact r⁻¹
end

@[hott] def ishae_impl_contr_fib {α : Type u} {β : Type v}
  (f : α → β) : ishae f → Π y, contr (fib f y)
| ⟨g, η, ε, τ⟩ := begin
  intro y, existsi (⟨g y, ε y⟩ : fib f y),
  intro g, induction g with x p, apply fib_eq,
  existsi (g # p)⁻¹ ⬝ η x, transitivity,
  { apply eq.map (⬝ p), apply types.equiv.map_functoriality },
  transitivity, apply eq.map (λ q, eq.map f (eq.map g p)⁻¹ ⬝ q ⬝ p),
  apply τ, transitivity, { symmetry, apply eq.assoc }, transitivity,
  { apply eq.map (⬝ (ε (f x) ⬝ p)), transitivity, apply eq.map_inv,
    apply eq.map types.eq.inv, symmetry, apply equiv.map_over_comp },
  apply types.equiv.rewrite_comp, transitivity,
  { apply eq.map (λ q, ε (f x) ⬝ q), symmetry, apply equiv.idmap },
  apply types.equiv.homotopy_square
end

@[hott] def comp_qinv₁ {α : Type u} {β : Type v} {γ : Type w}
  (f : α → β) (g : β → α) (H : is_qinv f g) :
  @qinv (γ → α) (γ → β) (λ (h : γ → α), f ∘ h) := begin
  existsi (λ h, g ∘ h), split;
  intro h; apply theorems.funext; intro x,
  apply H.pr₁, apply H.pr₂
end

@[hott] def comp_qinv₂ {α : Type u} {β : Type v} {γ : Type w}
  (f : α → β) (g : β → α) (H : is_qinv f g) :
  @qinv (β → γ) (α → γ) (λ (h : β → γ), h ∘ f) := begin
  existsi (λ h, h ∘ g), split;
  intro h; apply theorems.funext; intro x; apply eq.map h,
  apply H.pr₂, apply H.pr₁
end

@[hott] def linv_contr {α : Type u} {β : Type v}
  (f : α → β) (h : qinv f) : contr (linv f) := begin
  apply structures.contr_respects_equiv,
  { symmetry, apply sigma.respects_equiv,
    intro g, symmetry, apply @theorems.full α (λ _, α) (g ∘ f) },
  apply ishae_impl_contr_fib, apply qinv_impls_ishae,
  fapply comp_qinv₂, exact h.fst, exact h.snd
end

@[hott] def rinv_contr {α : Type u} {β : Type v}
  (f : α → β) (h : qinv f) : contr (rinv f) := begin
  apply structures.contr_respects_equiv,
  { symmetry, apply sigma.respects_equiv,
    intro g, symmetry, apply @theorems.full β (λ _, β) (f ∘ g) },
  apply ishae_impl_contr_fib, apply qinv_impls_ishae,
  fapply comp_qinv₁, exact h.fst, exact h.snd
end

@[hott] def product_contr {α : Type u} {β : Type v}
  (h : contr α) (g : contr β) : contr (α × β) := begin
  existsi (h.point, g.point), intro p,
  induction p with a b, fapply product.prod,
  apply h.intro, apply g.intro
end

@[hott] def biinv_prop {α : Type u} {β : Type v}
  (f : α → β) : prop (biinv f) := begin
  apply structures.lem_contr, intro g, apply product_contr,
  { apply linv_contr, apply qinv.of_biinv, assumption },
  { apply rinv_contr, apply qinv.of_biinv, assumption }
end

@[hott] theorem prop_exercise (π : Type u) : (prop π) ≃ (π ≃ ∥π∥) :=
begin
  existsi @prop_equiv π, split; existsi prop_from_equiv,
  { intro x, apply structures.prop_is_prop },
  { intro x,
    induction x with f H,
    induction H with linv rinv,
    induction linv with f α,
    induction rinv with g β,
    fapply sigma.prod,
    { apply theorems.funext, intro x, apply HITs.merely.uniq },
    { apply biinv_prop } }
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

@[hott] def propset.eq (α β : Ω) (h : α.fst = β.fst) : α = β :=
types.sigma.prod h (structures.prop_is_prop _ _)

end theorems.prop
end ground_zero