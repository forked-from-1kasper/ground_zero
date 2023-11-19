import GroundZero.HITs.Pushout
import GroundZero.Types.Unit

open GroundZero.Types.Equiv
open GroundZero.Types.Id
open GroundZero.Types

/-
  Suspension.
  * HoTT 6.5
-/

namespace GroundZero
namespace HITs

def Suspension.{u} (A : Type u) :=
@Pushout.{0, 0, u} 𝟏 𝟏 A (λ _, ★) (λ _, ★)

notation "∑ " => Suspension

namespace Suspension
  -- https://github.com/leanprover/lean2/blob/master/hott/homotopy/susp.hlean
  universe u v

  hott def north {A : Type u} : ∑ A := Pushout.inl ★
  hott def south {A : Type u} : ∑ A := Pushout.inr ★

  hott def merid {A : Type u} (x : A) : @Id (∑ A) north south :=
  Pushout.glue x

  hott def ind {A : Type u} {B : ∑ A → Type v} (n : B north) (s : B south)
    (m : Π x, n =[merid x] s) : Π x, B x :=
  Pushout.ind (λ ★, n) (λ ★, s) m

  attribute [eliminator] ind

  hott def rec {A : Type u} {B : Type v} (n s : B) (m : A → n = s) : ∑ A → B :=
  Pushout.rec (λ _, n) (λ _, s) m

  hott def indβrule {A : Type u} {B : ∑ A → Type v}
    (n : B north) (s : B south) (m : Π x, n =[merid x] s) (x : A) :
    apd (ind n s m) (merid x) = m x :=
  by apply Pushout.indβrule

  hott def recβrule {A : Type u} {B : Type v} (n s : B)
    (m : A → n = s) (x : A) : ap (rec n s m) (merid x) = m x :=
  by apply Pushout.recβrule

  instance (A : Type u) : isPointed (∑ A) := ⟨north⟩

  hott def σ {A : Type u} [isPointed A] : A → Ω¹(∑ A) :=
  λ x, merid x ⬝ (merid (pointOf A))⁻¹

  hott lemma σComMerid {A : Type u} [isPointed A] (x : A) : σ x ⬝ merid (pointOf A) = merid x :=
  by apply Id.cancelInvComp

  hott lemma σRevComMerid {A : Type u} [isPointed A] (x : A) : (σ x)⁻¹ ⬝ merid x = merid (pointOf A) :=
  begin apply rewriteComp; symmetry; apply σComMerid end

  section
    variable {A : Type u} [isPointed A] {n : ℕ}

    hott def suspΩ : Ωⁿ(A) → Ωⁿ⁺¹(∑ A) :=
    λ ε, conjugateΩ (compInv (merid (pointOf A))) (apΩ σ ε)

    hott lemma suspIdΩ : suspΩ (idΩ (pointOf A) n) = idΩ north (n + 1) :=
    begin transitivity; apply ap (conjugateΩ _); apply apIdΩ; apply conjugateIdΩ end

    hott lemma suspRevΩ (α : Ωⁿ⁺¹(A)) : suspΩ (revΩ α) = revΩ (suspΩ α) :=
    begin transitivity; apply ap (conjugateΩ _); apply apRevΩ; apply conjugateRevΩ end

    hott lemma suspMultΩ (α β : Ωⁿ⁺¹(A)) : suspΩ (comΩ α β) = comΩ (suspΩ α) (suspΩ β) :=
    begin transitivity; apply ap (conjugateΩ _); apply apFunctorialityΩ; apply conjugateComΩ end
  end
end Suspension

end HITs
end GroundZero
