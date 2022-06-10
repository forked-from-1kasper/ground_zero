import GroundZero.Algebra.Group.Subgroup
open GroundZero.Structures
open GroundZero.Theorems
open GroundZero.Types
open GroundZero.Proto
open GroundZero

/-
  Symmetric group.
  * https://en.wikipedia.org/wiki/Symmetric_group
-/

namespace GroundZero.Algebra
universe u

namespace Group
  variable {G : Group}

  -- Permutations
  hott def S.carrier (ε : 0-Type) := ε ≃₀ ε

  section
    variable {ε : 0-Type}

    hott def S.mul (p q : S.carrier ε) := Equiv.trans q p
    hott def S.one                     := Equiv.ideqv ε.1
    hott def S.inv (p : S.carrier ε)   := Equiv.symm p

    instance S.hasMul : Mul (S.carrier ε) := ⟨S.mul⟩
    instance S.hasOne : OfNat (S.carrier ε) (Nat.succ Nat.zero) := ⟨S.one⟩

    hott def S (ε : nType.{u} 0) : Group.{u} :=
    @Group.intro (ε ≃₀ ε) (Equiv.zeroEquiv.hset ε ε) S.mul S.inv S.one
      (λ _ _ _, Equiv.equivHmtpyLem _ _ (λ _, idp _))
      (λ _, Equiv.equivHmtpyLem _ _ (λ _, idp _))
      (λ _, Equiv.equivHmtpyLem _ _ (λ _, idp _))
      (λ e, Equiv.equivHmtpyLem _ _ (λ _, e.rightForward _))

    hott def left (G : Group) (x : G.carrier) : G.carrier ≃ G.carrier :=
    begin
      existsi (G.φ x ·); apply Prod.mk <;> existsi (G.φ (G.ι x) ·) <;> intro y;
      { transitivity; { symmetry; apply G.mulAssoc };
        transitivity; { apply Id.map (G.φ · y); apply G.mulLeftInv };
        apply G.oneMul };
      { transitivity; { symmetry; apply G.mulAssoc };
        transitivity; { apply Id.map (G.φ · y); apply mulRightInv };
        apply G.oneMul }
    end

    hott def S.univ (G : Group.{u}) : Hom G (S G.1.zero) :=
    mkhomo (left G)
      (begin
        intros x y; fapply Theorems.Equiv.equivHmtpyLem;
        intro; apply G.mulAssoc
      end)

    hott def S.univ.ker.encode : (ker (S.univ G)).set ⊆ (triv G).set :=
    begin
      intro x H; change _ = _; symmetry;
      apply unitOfSqr; apply Equiv.happlyEqv H
    end

    hott def S.univ.ker.decode : (triv G).set ⊆ (ker (S.univ G)).set :=
    begin
      intros x H; apply Theorems.Equiv.equivHmtpyLem;
      intro y; induction H using Id.casesOn; apply G.oneMul
    end

    noncomputable hott def S.univ.ker : ker (S.univ G) = triv G :=
    normal.ext (Ens.ssubset.asymm S.univ.ker.encode S.univ.ker.decode)
  end
end Group

end GroundZero.Algebra