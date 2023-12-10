import GroundZero.Types.Id
open GroundZero.Types

universe u v w w'

/--
  `Quot.withUseOf a b x` isn’t definitionally equal to `b` unless `x` is an constructor (i.e. `Quot.mk a`).

  It’s used to ensure that `Quot.withUseOf a₁ b x` and `Quot.withUseOf a₂ b x` aren’t
  definitionally equal unless `a₁` and `a₂` are.

  This is crucial in the definition of induction principles for HITs as there are
  *provably* unequal functions that definitionally agree on all point constructors
  (for examples see `HITs/Circle.lean`).

  See also:
  * https://github.com/gebner/hott3/blob/7ead7a8a2503049eacd45cbff6587802bae2add2/src/hott/init/hit.lean#L119-L129.
  * “The HoTT Library: A formalization of homotopy type theory in Coq” (https://arxiv.org/pdf/1610.04591.pdf), section 4.
-/
def Quot.withUseOf {X : Type u} {R : X → X → Sort 0} {A : Type v} {B : Type w} (a : A) (b : B) : Quot R → B :=
λ y, (@Quot.lift X R (A × B) (λ _, (a, b)) (λ _ _ _, rfl) y).2

section
  variable (X : Type u) (R : X → X → Sort 0) (A : Type u) (B : Type w) (a₁ a₂ : A) (b : B)
  #failure @Quot.withUseOf X R A B a₁ b ≡ @Quot.withUseOf X R A B a₂ b : Quot R → B
end

/--
  Behaves just like structure with one field of a given type `A`, but lacks definitional eta.

  Useful for defining HITs through Dan Licata’s trick (see https://github.com/gebner/hott3),
  because it seems impossible to define combinator similar to `Quot.withUseOf` for private structures
  in Lean 4 due to the availability of definitional eta for them.
-/
def Opaque (A : Type u) := @Quot A (λ _ _, False)

namespace EtaFailure
  inductive Opaque (A : Type u)
  | intro : A → Opaque A

  def withUseOf {X : Type u} {A : Type v} {B : Type w} (a : A) (b : B) : Opaque X → B :=
  λ y, (@Opaque.casesOn X (λ _, A × B) y (λ _, (a, b))).2

  variable (X : Type u) (A : Type u) (B : Type w) (a₁ a₂ : A) (b : B)

  #success @withUseOf X A B a₁ b ≡ @withUseOf X A B a₂ b : Opaque X → B

  variable (x : Opaque X)
  #success @withUseOf X A B a₁ b x ≡ b : B
  #success @withUseOf X A B a₂ b x ≡ b : B
end EtaFailure

namespace Opaque
  def intro {A : Type u} : A → Opaque A := Quot.mk (λ _ _, False)

  def elim {A : Type u} {B : Type v} (f : A → B) : Opaque A → B :=
  Quot.lift f (λ _ _ ε, nomatch ε)

  def elim₂ {A : Type u} {B : Type v} {C : Type w} (f : A → B → C) : Opaque A → Opaque B → C :=
  elim (elim ∘ f)

  def elim₃ {A : Type u} {B : Type v} {C : Type w} {D : Type w} (f : A → B → C → D) : Opaque A → Opaque B → Opaque C → D :=
  elim (elim₂ ∘ f)

  def value {A : Type u} : Opaque A → A := elim (λ x, x)

  def ind {A : Type u} {B : Opaque A → Type v} (f : Π x, B (intro x)) : Π x, B x :=
  λ x, Quot.hrecOn x f (λ _ _ ε, nomatch ε)
end Opaque

namespace GroundZero
  /--
    Used to postulate propositional computation rules for higher constructors.

    Shouldn’t be used directly (hence marked as `nothott`).
  -/
  opaque trustCoherence {A : Type u} {a b : A} {p q : a = b} : p = q :=
  match p, q with | idp _, idp _ => idp _

  /--
    Used to generate 1-path constructors out of `Quot.sound`.

    Should be used only within of `opaque` (hence marked as `nothott`).
  -/
  def trustHigherCtor {A : Type u} {a b : A} (p : Eq a b) : a = b :=
  begin induction p; reflexivity end

  attribute [nothott] trustCoherence trustHigherCtor

  hott def elimEq {A : Type u} {a b : A} (p : a = b) : Eq a b :=
  begin induction p; reflexivity end
end GroundZero
