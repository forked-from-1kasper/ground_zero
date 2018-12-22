import ground_zero.HITs.interval
open ground_zero.structures (prop hset)
open ground_zero.types.equiv (transport)
open ground_zero.types

namespace ground_zero
namespace theorems.prop

universes u v w

lemma transport_composition {α : Sort u} {a x₁ x₂ : α}
  (p : x₁ = x₂ :> α) (q : a = x₁ :> α) :
  transport (types.eq a) p q = q ⬝ p :> _ := begin
  induction p, symmetry, transitivity,
  apply eq.refl_right, trivial
end

theorem prop_is_set {α : Sort u} (r : prop α) : hset α := begin
  destruct r, intros f H,
  apply structures.hset.mk, intros, have g := f a,
  transitivity, symmetry, apply equiv.rewrite_comp,
  exact (equiv.apd g p)⁻¹ ⬝ transport_composition p (g a),
  induction q, apply types.eq.inv_comp
end

lemma prop_is_prop {α : Sort u} : prop (prop α) := begin
  apply structures.prop.mk,
  intros f g,
  have h := prop_is_set f, cases h,
  cases f, cases g,
  have p := λ a b, h (f a b) (g a b),
  apply eq.map structures.prop.mk,
  apply HITs.interval.dfunext, intro a,
  apply HITs.interval.dfunext, intro b,
  exact p a b
end

lemma prop_equiv {π : Type u} (h : prop π) : π ≃ ∥π∥ := begin
  existsi HITs.trunc.elem, split,
  repeat {
    existsi HITs.trunc.extract, intro x,
    simp [HITs.trunc.extract],
    simp [HITs.trunc.rec], simp [HITs.trunc.elem],
    intros, try { apply HITs.trunc.uniq },
    assumption
  }
end

lemma prop_from_equiv {π : Type u} (e : π ≃ ∥π∥) : prop π :=
begin
  apply structures.prop.mk,
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
  { intro x, apply prop_is_prop.intro },
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