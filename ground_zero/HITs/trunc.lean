import ground_zero.structures
open ground_zero.structures

namespace ground_zero.HITs
universes u v

hott theory

private structure trunc.aux (n : ℕ₋₂) (α : Type u) :=
(val : α)

def trunc (n : ℕ₋₂) (α : Type u) := trunc.aux n α

namespace trunc
  variables {α : Type u} {n : ℕ₋₂}
  attribute [nothott] trunc.aux.rec_on trunc.aux.rec

  @[hott] def elem (x : α) : trunc n α := aux.mk n x
  axiom uniq (n : ℕ₋₂) : is-n-type (trunc n α)

  @[safe] def ind {π : trunc n α → Type v}
    (elemπ : Π x, π (elem x))
    (uniqπ : Π x, is-n-type (π x)) : Π x, π x :=
  begin intro x, induction x, apply elemπ end
  attribute [irreducible] trunc

  @[hott] def rec {π : Type v}
    (elemπ : α → π)
    (uniqπ : is-n-type π) :
    trunc n α → π :=
  @ind α n (λ _, π) elemπ (λ _, uniqπ)

  notation `∥` α `∥₋₂` := trunc −2 α
  notation `∥` α `∥₋₁` := trunc −1 α
  notation `∥` α `∥₀`  := trunc  0 α
  notation `∥` α `∥₁`  := trunc  1 α

  @[hott] def elem_close {β : Type v} (G : is-n-type β)
    (f g : trunc n α → β) (H : f ∘ elem = g ∘ elem) : f = g := begin
    apply ground_zero.theorems.funext, fapply ind; intro x,
    { exact (λ (f : α → β), f x) # H },
    { apply hlevel.cumulative, assumption }
  end

  @[hott] noncomputable def nth_trunc (H : is-n-type α) : α ≃ trunc n α := begin
    existsi elem, split; existsi rec id H,
    { intro x, trivial },
    { apply ground_zero.HITs.interval.happly,
      apply elem_close, apply uniq,
      apply ground_zero.theorems.funext,
      intro x, trivial }
  end

  @[hott] noncomputable def set_equiv {α : Type u} (H : hset α) : α ≃ ∥α∥₀ :=
  begin apply nth_trunc, apply zero_eqv_set.left, assumption end
end trunc

end ground_zero.HITs