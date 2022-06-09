import GroundZero.Structures
open GroundZero.Structures

namespace GroundZero.HITs
universe u v w

private structure Trunc.aux (n : ℕ₋₂) (A : Type u) :=
(val : A)

def Trunc (n : ℕ₋₂) (A : Type u) := Trunc.aux n A

namespace Trunc
  variable {A : Type u} {n : ℕ₋₂}
  attribute [nothott] Trunc.aux.recOn Trunc.aux.rec aux.val

  hott def elem (x : A) : Trunc n A := aux.mk x
  axiom uniq (n : ℕ₋₂) : is-n-type (Trunc n A)

  notation "∥" A "∥₋₂" => Trunc −2 A
  notation "∥" A "∥₋₁" => Trunc −1 A

  macro "∥" A:term "∥" n:subscript : term => do
    `(Trunc $(← Meta.Notation.parseSubscript n) $A)

  macro "|" x:term "|" n:subscript : term => do
    `(@Trunc.elem _ $(← Meta.Notation.parseSubscript n) $x)

  @[hottAxiom, eliminator] def ind {B : Trunc n A → Type v}
    (elemπ : Π x, B (elem x)) (uniqπ : Π x, is-n-type (B x)) : Π x, B x :=
  begin intro x; induction x using Trunc.aux.casesOn; apply elemπ end

  attribute [irreducible] Trunc

  hott def rec {B : Type v} (elemπ : A → B) (uniqπ : is-n-type B) : ∥A∥ₙ → B :=
  @ind A n (λ _, B) elemπ (λ _, uniqπ)

  hott def elemClose {B : Type v} (G : is-n-type B)
    (f g : ∥A∥ₙ → B) (H : f ∘ elem = g ∘ elem) : f = g :=
  begin
    apply GroundZero.Theorems.funext; fapply ind <;> intro x;
    { exact Types.Id.map (λ (f : A → B), f x) H };
    { apply hlevel.cumulative; assumption }
  end

  noncomputable hott def nthTrunc (H : is-n-type A) : A ≃ ∥A∥ₙ :=
  begin
    existsi elem; apply Prod.mk <;> existsi rec id H;
    { intro x; reflexivity };
    { apply GroundZero.HITs.Interval.happly;
      apply elemClose; apply uniq;
      apply GroundZero.Theorems.funext;
      intro x; reflexivity }
  end

  noncomputable hott def setEquiv {A : Type u} (H : hset A) : A ≃ ∥A∥₀ :=
  begin apply nthTrunc; apply zeroEqvSet.left; assumption end

  noncomputable hott def lift {A : Type u} {B : Type v} {n : ℕ₋₂} (f : A → B) : ∥A∥ₙ → ∥B∥ₙ :=
  rec (elem ∘ f) (uniq n)

  noncomputable hott def lift₂ {A : Type u} {B : Type v} {C : Type w} {n : ℕ₋₂}
    (f : A → B → C) : ∥A∥ₙ → ∥B∥ₙ → ∥C∥ₙ :=
  rec (lift ∘ f) (piRespectsNType n (λ _, uniq n))
end Trunc

end GroundZero.HITs