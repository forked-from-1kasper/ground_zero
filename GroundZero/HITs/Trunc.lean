import GroundZero.Structures
open GroundZero.Structures

namespace GroundZero.HITs
universe u v w

private structure Trunc.aux (n : ℕ₋₂) (α : Type u) :=
(val : α)

def Trunc (n : ℕ₋₂) (α : Type u) := Trunc.aux n α

namespace Trunc
  variable {α : Type u} {n : ℕ₋₂}
  attribute [nothott] Trunc.aux.recOn Trunc.aux.rec aux.val

  hott def elem (x : α) : Trunc n α := aux.mk x
  axiom uniq (n : ℕ₋₂) : is-n-type (Trunc n α)

  notation "∥" α "∥₋₂" => Trunc −2 α
  notation "∥" α "∥₋₁" => Trunc −1 α

  notation "|" x "|₋₂" => elem x −2
  notation "|" x "|₋₁" => elem x −1

  macro "∥" α:term "∥" n:many1(subscriptNumeral) : term =>
    `(Trunc $(Meta.Notation.parseSubNumber n) $α)

  macro "∥" α:term "∥" i:many1(subscriptChar) : term =>
    `(Trunc $(Lean.mkIdent (Meta.Notation.parseSubIdent i)) $α)

  macro "|" x:term "|" n:many1(subscriptNumeral) : term =>
    `(@Trunc.elem _ $(Meta.Notation.parseSubNumber n) $x)

  macro "|" x:term "|" i:many1(subscriptChar) : term =>
    `(@Trunc.elem _ $(Lean.mkIdent (Meta.Notation.parseSubIdent i)) $x)

  @[hottAxiom, eliminator] def ind {π : Trunc n α → Type v}
    (elemπ : Π x, π (elem x))
    (uniqπ : Π x, is-n-type (π x)) : Π x, π x :=
  begin intro x; induction x using Trunc.aux.casesOn; apply elemπ end
  attribute [irreducible] Trunc

  hott def rec {π : Type v} (elemπ : α → π) (uniqπ : is-n-type π) : Trunc n α → π :=
  @ind α n (λ _, π) elemπ (λ _, uniqπ)

  hott def elemClose {β : Type v} (G : is-n-type β)
    (f g : ∥α∥ₙ → β) (H : f ∘ elem = g ∘ elem) : f = g :=
  begin
    apply GroundZero.Theorems.funext; fapply ind <;> intro x;
    { exact Types.Id.map (λ (f : α → β), f x) H };
    { apply hlevel.cumulative; assumption }
  end

  noncomputable hott def nthTrunc (H : is-n-type α) : α ≃ ∥α∥ₙ :=
  begin
    existsi elem; apply Prod.mk <;> existsi rec id H;
    { intro x; reflexivity };
    { apply GroundZero.HITs.Interval.happly;
      apply elemClose; apply uniq;
      apply GroundZero.Theorems.funext;
      intro x; reflexivity }
  end

  noncomputable hott def setEquiv {α : Type u} (H : hset α) : α ≃ ∥α∥₀ :=
  begin apply nthTrunc; apply zeroEqvSet.left; assumption end

  noncomputable hott def lift {α : Type u} {β : Type v} {n : ℕ₋₂} (f : α → β) : ∥α∥ₙ → ∥β∥ₙ :=
  rec (elem ∘ f) (uniq n)

  noncomputable hott def lift₂ {α : Type u} {β : Type v} {γ : Type w} {n : ℕ₋₂}
    (f : α → β → γ) : ∥α∥ₙ → ∥β∥ₙ → ∥γ∥ₙ :=
  rec (lift ∘ f) (piRespectsNType n (λ _, uniq n))
end Trunc

end GroundZero.HITs