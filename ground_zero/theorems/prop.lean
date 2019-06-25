import ground_zero.HITs.interval ground_zero.HITs.truncation ground_zero.types.sigma
open ground_zero.structures (prop contr hset prop_is_set)
open ground_zero.types.equiv (transport transport_composition)
open ground_zero.types

namespace ground_zero
namespace theorems.prop

universes u v w

def product_prop {α : Sort u} {β : Sort v}
  (h : prop α) (g : prop β) : prop (α × β) := begin
  intros a b,
  cases a with x y, cases b with u v,
  have p := h x u, have q := g y v,
  induction p, induction q, reflexivity
end

def prop_equiv_lemma {α : Sort u} {β : Sort v}
  (F : prop α) (G : prop β) (f : α → β) (g : β → α) : α ≃ β :=
begin
  existsi f, split; existsi g,
  { intro x, apply F }, { intro y, apply G }
end

def contr_equiv_unit {α : Sort u} (h : contr α) : α ≃ types.unit := begin
  existsi (λ _, types.unit.star), split;
  existsi (λ _, h.point),
  { intro x, apply h.intro },
  { intro x, cases x, reflexivity }
end

lemma uniq_does_not_add_new_paths {α : Sort u} (a b : ∥α∥) (p : a = b :> ∥α∥) :
  HITs.truncation.uniq a b = p :> a = b :> ∥α∥ :=
prop_is_set HITs.truncation.uniq (HITs.truncation.uniq a b) p

lemma prop_is_prop {α : Sort u} : prop (prop α) := begin
  intros f g,
  have p := λ a b, (prop_is_set f) (f a b) (g a b),
  apply HITs.interval.dfunext, intro a,
  apply HITs.interval.dfunext, intro b,
  exact p a b
end

def prop_equiv {π : Type u} (h : prop π) : π ≃ ∥π∥ := begin
  existsi HITs.truncation.elem,
  split; existsi (HITs.truncation.rec h id); intro x,
  { reflexivity },
  { apply HITs.truncation.uniq }
end

def prop_from_equiv {π : Type u} (e : π ≃ ∥π∥) : prop π := begin
  cases e with f H, cases H with linv rinv,
  cases linv with g α, cases rinv with h β,
  intros a b,
  transitivity, exact (α a)⁻¹,
  symmetry, transitivity, exact (α b)⁻¹,
  apply eq.map g, exact HITs.truncation.uniq (f b) (f a)
end

def biinv_prop {α : Sort u} {β : Sort v} (f : α → β) : prop (types.equiv.biinv f) := begin
  intros m n, cases m with linv₁ rinv₁, cases n with linv₂ rinv₂,
  cases rinv₁ with g G, cases rinv₂ with h H,
  cases linv₁ with g' G', cases linv₂ with h' H',
  { apply types.product.eq,
    { fapply types.sigma.prod,
      { apply HITs.interval.funext, intro x,
        transitivity, symmetry, apply H',
        transitivity, apply types.eq.map h',
        fapply types.qinv.rinv_inv f g g' G G',
        trivial },
      { admit } },
    { fapply types.sigma.prod,
      { apply HITs.interval.funext, intro x,
        transitivity, symmetry, apply types.eq.map, apply H,
        transitivity, fapply types.qinv.linv_inv f g g' G G',
        trivial },
      { admit } } },
end 

theorem prop_exercise (π : Type u) : (prop π) ≃ (π ≃ ∥π∥) :=
begin
  existsi @prop_equiv π, split; existsi prop_from_equiv,
  { intro x, apply prop_is_prop },
  { intro x, simp,
    cases x with f H,
    cases H with linv rinv,
    cases linv with f α,
    cases rinv with g β,
    fapply sigma.prod,
    { apply HITs.interval.funext, intro x, apply HITs.truncation.uniq },
    { apply biinv_prop } }
end

lemma comp_qinv₁ {α : Sort u} {β : Sort v} {γ : Sort w}
  (f : α → β) (g : β → α) (H : is_qinv f g) :
  qinv (λ (h : γ → α), f ∘ h) := begin
  existsi (λ h, g ∘ h), split,
  { intro h, apply HITs.interval.funext,
    intro x, exact H.pr₁ (h x) },
  { intro h, apply HITs.interval.funext,
    intro x, exact H.pr₂ (h x) }
end

lemma comp_qinv₂ {α : Sort u} {β : Sort v} {γ : Sort w}
  (f : α → β) (g : β → α) (H : is_qinv f g) :
  qinv (λ (h : β → γ), h ∘ f) := begin
  existsi (λ h, h ∘ g), split,
  { intro h, apply HITs.interval.funext,
    intro x, apply eq.map h, exact H.pr₂ x },
  { intro h, apply HITs.interval.funext,
    intro x, apply eq.map h, exact H.pr₁ x }
end

def lem_contr_inv {α : Sort u} (h : prop α) (x : α) : contr α := ⟨x, h x⟩

def lem_contr_equiv {α : Sort u} : (prop α) ≃ (α → contr α) := begin
  apply prop_equiv_lemma,
  { apply structures.prop_is_prop },
  { apply structures.function_to_contr },
  apply lem_contr_inv, apply structures.lem_contr
end

end theorems.prop
end ground_zero