import ground_zero.HITs.interval ground_zero.HITs.merely
import ground_zero.theorems.ua
open ground_zero.structures (prop contr hset propset prop_is_set)
open ground_zero.HITs.interval
open ground_zero.types.equiv
open ground_zero.types

namespace ground_zero
namespace theorems.prop

hott theory

universes u v w

@[hott] lemma uniq_does_not_add_new_paths {α : Type u} (a b : ∥α∥) (p : a = b) :
  HITs.merely.uniq a b = p :=
prop_is_set HITs.merely.uniq (HITs.merely.uniq a b) p

@[hott] def prop_equiv {π : Type u} (h : prop π) : π ≃ ∥π∥ :=
begin
  existsi HITs.merely.elem,
  split; existsi (HITs.merely.rec h id); intro x,
  { reflexivity },
  { apply HITs.merely.uniq }
end

@[hott] def prop_from_equiv {π : Type u} (e : π ≃ ∥π∥) : prop π :=
begin
  cases e with f H, cases H with linv rinv,
  cases linv with g α, cases rinv with h β,
  intros a b,
  transitivity, exact (α a)⁻¹,
  symmetry, transitivity, exact (α b)⁻¹,
  apply Id.map g, exact HITs.merely.uniq (f b) (f a)
end

@[hott] def map_to_happly {α : Type u} {β : Type v}
  (c : α) (f g : α → β) (p : f = g) :
  (λ (f : α → β), f c) # p = happly p c :=
begin induction p, trivial end

@[hott] def hmtpy_rewrite {α : Type u} (f : α → α) (H : f ~ proto.idfun) :
  Π x, H (f x) = f # (H x) :=
begin
  intro x,
  symmetry, transitivity, { symmetry, apply Id.refl_right }, transitivity,
  { apply Id.map (λ p, f # (H x) ⬝ p), symmetry, apply Id.comp_inv (H x) },
  transitivity, { apply Id.assoc },
  transitivity, { apply Id.map (⬝ (H x)⁻¹), symmetry, apply equiv.homotopy_square },
  transitivity, { symmetry, apply Id.assoc },
  transitivity, { apply Id.map (λ p, H (f x) ⬝ (p ⬝ (H x)⁻¹)), apply equiv.idmap },
  transitivity, { apply Id.map (λ p, H (f x) ⬝ p), apply Id.comp_inv },
  apply Id.refl_right
end

@[hott] def qinv_impls_ishae {α : Type u} {β : Type v}
  (f : α → β) : qinv f → ishae f :=
begin
  intro H, cases H with g H, cases H with ε η,
  let ε' := λ b, (ε (f (g b)))⁻¹ ⬝ (@Id.map α β _ _ f (η (g b)) ⬝ ε b),
  existsi g, existsi η, existsi ε', intro x,
  symmetry, transitivity,
  { apply Id.map (λ p, (ε (f (g (f x))))⁻¹ ⬝ ((@Id.map α β _ _ f p) ⬝ ε (f x))),
    apply hmtpy_rewrite (g ∘ f) },
  apply types.equiv.rewrite_comp, transitivity,
  { apply Id.map (⬝ ε (f x)), symmetry,
    apply equiv.map_over_comp (g ∘ f) },
  symmetry, apply @equiv.homotopy_square α β (f ∘ g ∘ f) f
                    (λ x, ε (f x)) (g (f x)) x (η x)
end

@[hott] def respects_equiv_over_fst {α : Type u} {β : Type v}
  (φ : α ≃ β) (C : α → Type w) : (Σ x, C x) ≃ (Σ x, C (φ.left x)) :=
begin
  fapply sigma.replace_ishae, apply qinv_impls_ishae,
  existsi φ.1, split, apply φ.left_forward, apply φ.forward_left
end

@[hott] def fib_eq {α : Type u} {β : Type v} (f : α → β) {y : β}
  {a b : α} (p : f a = y) (q : f b = y) (H : Σ (γ : a = b), f # γ ⬝ q = p) :
  ⟨a, p⟩ = ⟨b, q⟩ :> fib f y :=
begin
  induction H with γ r, fapply sigma.prod, exact γ,
  transitivity, { apply types.equiv.transport_over_contr_map },
  transitivity, { apply Id.map (⬝ p), apply types.Id.map_inv },
  apply equiv.rewrite_comp, exact r⁻¹
end

@[hott] def ishae_impl_contr_fib {α : Type u} {β : Type v}
  (f : α → β) : ishae f → Π y, contr (fib f y)
| ⟨g, η, ε, τ⟩ := begin
  intro y, existsi (⟨g y, ε y⟩ : fib f y),
  intro g, induction g with x p, apply fib_eq,
  existsi (g # p)⁻¹ ⬝ η x, transitivity,
  { apply Id.map (⬝ p), apply types.equiv.map_functoriality },
  transitivity, apply Id.map (λ q, Id.map f (Id.map g p)⁻¹ ⬝ q ⬝ p),
  apply τ, transitivity, { symmetry, apply Id.assoc }, transitivity,
  { apply Id.map (⬝ (ε (f x) ⬝ p)), transitivity, apply Id.map_inv,
    apply Id.map types.Id.inv, symmetry, apply equiv.map_over_comp },
  apply types.equiv.rewrite_comp, transitivity,
  { apply Id.map (λ q, ε (f x) ⬝ q), symmetry, apply equiv.idmap },
  apply types.equiv.homotopy_square
end

@[hott] def comp_qinv₁ {α : Type u} {β : Type v} {γ : Type w}
  (f : α → β) (g : β → α) (H : is_qinv f g) :
  @qinv (γ → α) (γ → β) (λ (h : γ → α), f ∘ h) :=
begin
  existsi (λ h, g ∘ h), split;
  intro h; apply theorems.funext; intro x,
  apply H.pr₁, apply H.pr₂
end

@[hott] def comp_qinv₂ {α : Type u} {β : Type v} {γ : Type w}
  (f : α → β) (g : β → α) (H : is_qinv f g) :
  @qinv (β → γ) (α → γ) (λ (h : β → γ), h ∘ f) :=
begin
  existsi (λ h, h ∘ g), split;
  intro h; apply theorems.funext; intro x; apply Id.map h,
  apply H.pr₂, apply H.pr₁
end

@[hott] def linv_contr {α : Type u} {β : Type v}
  (f : α → β) (h : qinv f) : contr (linv f) :=
begin
  apply structures.contr_respects_equiv,
  { symmetry, apply sigma.respects_equiv,
    intro g, symmetry, apply @theorems.full α (λ _, α) (g ∘ f) },
  apply ishae_impl_contr_fib, apply qinv_impls_ishae,
  fapply comp_qinv₂, exact h.fst, exact h.snd
end

@[hott] def rinv_contr {α : Type u} {β : Type v}
  (f : α → β) (h : qinv f) : contr (rinv f) :=
begin
  apply structures.contr_respects_equiv,
  { symmetry, apply sigma.respects_equiv,
    intro g, symmetry, apply @theorems.full β (λ _, β) (f ∘ g) },
  apply ishae_impl_contr_fib, apply qinv_impls_ishae,
  fapply comp_qinv₁, exact h.fst, exact h.snd
end

@[hott] def product_contr {α : Type u} {β : Type v}
  (h : contr α) (g : contr β) : contr (α × β) :=
begin
  existsi (h.point, g.point), intro p,
  induction p with a b, fapply product.prod,
  apply h.intro, apply g.intro
end

@[hott] def biinv_prop {α : Type u} {β : Type v}
  (f : α → β) : prop (biinv f) :=
begin
  apply structures.lem_contr, intro g, apply product_contr,
  { apply linv_contr, apply qinv.of_biinv, assumption },
  { apply rinv_contr, apply qinv.of_biinv, assumption }
end

@[hott] def equiv_hmtpy_lem {α : Type u} {β : Type v}
  (f g : α ≃ β) (H : f.forward ~ g.forward) : f = g :=
begin
  fapply sigma.prod,
  { apply theorems.funext, exact H },
  { apply biinv_prop }
end

@[hott] def prop_equiv_prop {α β : Type u} (G : prop β) : prop (α ≃ β) :=
begin intros f g, apply theorems.prop.equiv_hmtpy_lem, intro x, apply G end

@[hott] def prop_exercise (π : Type u) : (prop π) ≃ (π ≃ ∥π∥) :=
begin
  existsi @prop_equiv π, split; existsi prop_from_equiv,
  { intro x, apply structures.prop_is_prop },
  { intro x, induction x with f H,
    induction H with linv rinv,
    induction linv with f α,
    induction rinv with g β,
    apply equiv_hmtpy_lem,
    intro x, apply HITs.merely.uniq }
end

@[hott] def lem_contr_inv {α : Type u} (h : prop α) (x : α) : contr α := ⟨x, h x⟩

@[hott] def lem_contr_equiv {α : Type u} : (prop α) ≃ (α → contr α) :=
begin
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
  (Σ x, β x) ≃ β h.point :=
begin
  existsi contr_to_type h, split;
  existsi @type_to_contr α β h; intro x,
  { cases x with x u, fapply types.sigma.prod,
    { apply h.intro },
    { apply types.equiv.transport_back_and_forward } },
  { transitivity, apply Id.map (λ p, types.equiv.subst p x),
    apply prop_is_set (structures.contr_impl_prop h) _ Id.refl,
    trivial }
end

@[hott] def propset.Id (α β : Ω) (h : α.fst = β.fst) : α = β :=
types.sigma.prod h (structures.prop_is_prop _ _)

@[hott] noncomputable def prop_eq_prop {α β : Type u} (G : prop β) : prop (α = β) :=
begin
  apply structures.prop_respects_equiv,
  apply ground_zero.ua.univalence α β,
  apply theorems.prop.prop_equiv_prop G
end

@[hott] noncomputable def propset_is_set : hset propset :=
begin
  intros x y, induction x with x H, induction y with y G,
  apply transport (λ π, Π (p q : π), p = q),
  symmetry, apply ground_zero.ua, apply types.sigma.sigma_path,
  intros p q, induction p with p p', induction q with q q',
  change x = y at p, change x = y at q, fapply types.sigma.prod,
  { apply prop_eq_prop, exact G },
  { apply prop_is_set, apply structures.prop_is_prop }
end

@[hott] def hset_equiv {α : Type u} {β : Type v} (g : hset β) : hset (α ≃ β) :=
begin
  fapply structures.hset_respects_sigma,
  { apply structures.pi_hset, intro x, assumption },
  { intro x, apply structures.prop_is_set,
    apply theorems.prop.biinv_prop }
end

@[hott] def bool.decode : 𝟐 ≃ 𝟐 → 𝟐 :=
λ e, e.fst ff

@[hott] def bool.encode : 𝟐 → 𝟐 ≃ 𝟐
| ff := equiv.id 𝟐
| tt := ua.neg_bool_equiv

@[hott] def eqv_inj {α : Type u} {β : Type v}
  (e : α ≃ β) (x y : α) (p : e.forward x = e.forward y) : x = y :=
begin
  transitivity, symmetry, apply e.left_forward,
  transitivity, apply Id.map e.left, exact p,
  apply e.left_forward
end

@[hott] def bool_equiv_eqv_bool : (𝟐 ≃ 𝟐) ≃ 𝟐 :=
begin
  fapply sigma.mk, exact bool.decode, fapply qinv.to_biinv,
  fapply sigma.mk, exact bool.encode, split,
  { intro x, induction x; reflexivity },
  { intro e, induction e with φ e, apply theorems.prop.equiv_hmtpy_lem,
    intro x, cases structures.bool_eq_total (φ ff) with p₁ q₁;
    cases structures.bool_eq_total (φ tt) with p₂ q₂;
    { apply proto.empty.elim, apply structures.ff_neq_tt,
      apply eqv_inj ⟨φ, e⟩, exact p₁ ⬝ p₂⁻¹ <|> exact q₁ ⬝ q₂⁻¹ } <|>
    { transitivity, apply Id.map (λ (ψ : 𝟐), (bool.encode ψ).forward x),
      exact p₁ <|> exact q₁, symmetry, cases x; assumption } }
end

@[hott] def corr_of_qinv {α : Type u} {β : Type v} : qinv.eqv α β → corr α β :=
begin
  intro w, existsi (λ a b, b = w.1 a), split; intros,
  { apply structures.contr_respects_equiv,
    apply sigma.hmtpy_inv_eqv, apply singl.contr },
  { apply structures.contr_respects_equiv,
    apply respects_equiv_over_fst (qinv.to_equiv (qinv.inv w)) (Id b),
    apply singl.contr }
end

@[hott] def qinv_of_corr {α : Type u} {β : Type v} : corr α β → qinv.eqv α β :=
begin
  intro w, fapply sigma.mk, intro a, apply (w.2.1 a).point.1,
  fapply sigma.mk, intro b, apply (w.2.2 b).point.1, split,
  { intro b, apply sigma.fst # ((w.2.1 (w.2.2 b).point.1).intro ⟨b, (w.2.2 b).point.2⟩) },
  { intro a, apply sigma.fst # ((w.2.2 (w.2.1 a).point.1).intro ⟨a, (w.2.1 a).point.2⟩) }
end

section
  variables {α : Type u} {β : Type v} (e : qinv.eqv α β)

  @[hott] example : (qinv_of_corr (corr_of_qinv e)).1 = e.1     := by reflexivity
  @[hott] example : (qinv_of_corr (corr_of_qinv e)).2.1 = e.2.1 := by reflexivity
end

end theorems.prop
end ground_zero