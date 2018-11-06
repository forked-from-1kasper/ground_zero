import ground_zero.interval
open ground_zero.structures (prop hset)

namespace ground_zero
namespace prop

universe u

theorem prop_is_set {α : Sort u} (r : prop α) : hset α := begin
  destruct r, intros h H,
  apply structures.hset.mk,
  intros, admit
end

lemma prop_is_prop {α : Sort u} : prop (prop α) := begin
  apply ground_zero.structures.prop.mk,
  intros f g,
  have h := prop_is_set f, cases h,
  cases f, cases g,
  have j := λ a b, h (f a b) (g a b),
  apply eq.map structures.prop.mk,
  apply interval.dfunext, intro a,
  apply interval.dfunext, intro b,
  exact j a b
end

lemma prop_equiv {π : Type u} (h : prop π) : π ≃ ∥π∥ := begin
  existsi trunc.elem, split,
  repeat {
    existsi trunc.extract, intro x,
    simp [trunc.extract],
    simp [trunc.rec], simp [trunc.elem],
    intros, try { apply trunc.uniq },
    assumption
  }
end

lemma prop_from_equiv {π : Type u} (e : π ≃ ∥π∥) : prop π :=
begin
  apply structures.prop.mk,
  cases e with f H, cases H with linv rinv,
  cases linv with g α, cases rinv with h β,
  intros a b,
  have p : Π (x : π), eq (g (f x)) x := α,
  rw [←ground_zero.support.truncation (p a)],
  rw [←ground_zero.support.truncation (p b)],
  rw [support.truncation (trunc.uniq (f a) (f b))]
end

theorem prop_exercise (π : Type u) : (prop π) ≃ (π ≃ ∥π∥) :=
begin
  existsi @prop_equiv π, split; existsi prop_from_equiv,
  { intro x, simp, cases x,
    have p := @prop_is_prop π,
    cases p, apply p },
  { intro x, simp,
    cases x with f H,
    cases H with linv rinv,
    cases linv with f α,
    cases rinv with g β,
    admit }
end

end prop
end ground_zero