import ground_zero.HITs.interval
open ground_zero.structures (prop hset prop_is_set)
open ground_zero.types.equiv (transport transport_composition)
open ground_zero.types

namespace ground_zero
namespace theorems.prop

universes u v w

lemma product_prop {α : Sort u} {β : Sort v}
  (h : prop α) (g : prop β) : prop (α × β) := begin
  intros a b,
  cases a with x y, cases b with u v,
  have p := h x u, have q := g y v,
  induction p, induction q, reflexivity
end

lemma uniq_does_not_add_new_paths {α : Sort u} (a b : ∥α∥) (p : a = b :> ∥α∥) :
  HITs.trunc.uniq a b = p :> a = b :> ∥α∥ :=
prop_is_set HITs.trunc.uniq (HITs.trunc.uniq a b) p

lemma prop_is_prop {α : Sort u} : prop (prop α) := begin
  intros f g,
  have p := λ a b, (prop_is_set f) (f a b) (g a b),
  apply HITs.interval.dfunext, intro a,
  apply HITs.interval.dfunext, intro b,
  exact p a b
end

lemma prop_equiv {π : Type u} (h : prop π) : π ≃ ∥π∥ := begin
  existsi HITs.trunc.elem,
  split; existsi (HITs.trunc.extract h); intro x,
  { reflexivity },
  { apply HITs.trunc.uniq }
end

lemma prop_from_equiv {π : Type u} (e : π ≃ ∥π∥) : prop π := begin
  cases e with f H, cases H with linv rinv,
  cases linv with g α, cases rinv with h β,
  intros a b,
  transitivity, exact (α a)⁻¹,
  symmetry, transitivity, exact (α b)⁻¹,
  apply eq.map g, exact HITs.trunc.uniq (f b) (f a)
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
    admit }
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

end theorems.prop
end ground_zero