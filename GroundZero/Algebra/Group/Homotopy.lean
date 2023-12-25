import GroundZero.Algebra.Group.Basic
import GroundZero.HITs.Trunc

open GroundZero.Types.Id (idΩ ap)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types
open GroundZero.HITs

universe u

namespace GroundZero.Algebra

namespace Homotopy
  variable {A : Type u} {x : A} {n : ℕ}

  hott definition mul : ∥Ωⁿ⁺¹(A, x)∥₀ → ∥Ωⁿ⁺¹(A, x)∥₀ → ∥Ωⁿ⁺¹(A, x)∥₀ :=
  Trunc.ap₂ comΩ

  hott definition inv : ∥Ωⁿ⁺¹(A, x)∥₀ → ∥Ωⁿ⁺¹(A, x)∥₀ :=
  Trunc.ap revΩ

  hott definition unit : ∥Ωⁿ(A, x)∥₀ :=
  |idΩ x n|₀

  hott lemma isAssoc (a b c : ∥Ωⁿ⁺¹(A, x)∥₀) : mul (mul a b) c = mul a (mul b c) :=
  begin
    induction a; induction b; induction c; transitivity;
    apply Trunc.apβrule₂; apply ap Trunc.elem; symmetry; apply assocΩ;
    -- TODO: write some tactic to solve this automatically?
    apply hlevel.cumulative; apply Trunc.uniq 0;
    apply hlevel.cumulative; apply Trunc.uniq 0;
    apply hlevel.cumulative; apply Trunc.uniq 0
  end

  hott lemma hasLeftUnit (a : ∥Ωⁿ⁺¹(A, x)∥₀) : mul unit a = a :=
  begin
    induction a; transitivity; apply Trunc.apβrule₂; apply ap Trunc.elem;
    apply lidΩ; apply hlevel.cumulative; apply Trunc.uniq 0
  end

  hott lemma hasLeftInverse (a : ∥Ωⁿ⁺¹(A, x)∥₀) : mul (inv a) a = unit :=
  begin
    induction a; transitivity; apply Trunc.apβrule₂; apply ap Trunc.elem;
    apply revlΩ; apply hlevel.cumulative; apply Trunc.uniq 0
  end

  hott lemma isAbelian (a b : ∥Ωⁿ⁺²(A, x)∥₀) : mul a b = mul b a :=
  begin
    induction a; induction b; transitivity; apply Trunc.apβrule₂;
    apply ap Trunc.elem; apply abelianComΩ;
    apply hlevel.cumulative; apply Trunc.uniq 0;
    apply hlevel.cumulative; apply Trunc.uniq 0
  end
end Homotopy

hott definition Homotopy {A : Type u} (a : A) (n : ℕ) : Group :=
@Group.intro ∥Ωⁿ⁺¹(A, a)∥₀ (zeroEqvSet.forward (Trunc.uniq 0))
  Homotopy.mul Homotopy.inv Homotopy.unit Homotopy.isAssoc
  Homotopy.hasLeftUnit Homotopy.hasLeftInverse

def zws := Char.mk 0x200B (by decide)
def ZWS := leading_parser zws.toString

macro:max "π" noWs ZWS noWs n:subscript noWs "(" τ:term ")" : term => do
  `(Homotopy (pointOf $τ) (Nat.pred $(← Meta.Notation.parseSubscript n)))

macro:max "π" noWs ZWS noWs n:subscript noWs "(" τ:term ", " ε:term ")" : term => do
  `(@Homotopy $τ $ε (Nat.pred $(← Meta.Notation.parseSubscript n)))

macro:max "π" noWs "[" n:term "]" "(" τ:term ")" : term => do
  `(Homotopy (pointOf $τ) (Nat.pred $n))

macro:max "π" noWs "[" n:term "]" "(" τ:term ", " ε:term ")" : term => do
  `(@Homotopy $τ $ε (Nat.pred $n))

variable (A : Type) (a : A) (n : ℕ)

#check π[2](A, a)
--#check πₙ(A, a)

#check λ n, π​ₙ₊₂(A, a)

end GroundZero.Algebra
