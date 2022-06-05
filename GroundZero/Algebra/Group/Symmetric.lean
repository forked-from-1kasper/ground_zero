import GroundZero.Algebra.Group.Subgroup
open GroundZero.Structures
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
  --open GroundZero.Algebra.Pregroup (right_div left_div conjugate conjugate_rev subgroup)

  variable {G : Pregroup} [Algebra.group G]

  -- Permutations
  hott def S.carrier (ε : 0-Type) := ε ≃₀ ε

  section
    variable {ε : 0-Type}

    hott def S.mul (p q : S.carrier ε) := Equiv.trans q p
    hott def S.one                     := Equiv.ideqv ε.1
    hott def S.inv (p : S.carrier ε)   := Equiv.symm p

    instance S.hasMul : Mul (S.carrier ε) := ⟨S.mul⟩
    instance S.hasOne : OfNat (S.carrier ε) (Nat.succ Nat.zero) := ⟨S.one⟩

    section
      hott def S (ε : nType.{u} 0) : Pregroup.{u} :=
      @Pregroup.intro (ε ≃₀ ε) (Theorems.Prop.zeroEquiv.hset ε ε) S.mul S.inv S.one

      instance S.semigroup : semigroup (S ε).magma :=
      ⟨begin intros; fapply Theorems.Prop.equivHmtpyLem; intro x; reflexivity end⟩

      instance S.monoid : monoid (S ε).premonoid :=
      ⟨@S.semigroup ε,
       begin intro; fapply Theorems.Prop.equivHmtpyLem; intro; reflexivity end,
       begin intro; fapply Theorems.Prop.equivHmtpyLem; intro; reflexivity end⟩

      instance S.group : group (S ε) :=
      ⟨S.monoid, begin
        intro ⟨f, (⟨g, G⟩, ⟨h, H⟩)⟩; fapply Theorems.Prop.equivHmtpyLem;
        intro x; change h (f x) = x; apply Qinv.linvInv; exact H; exact G
      end⟩
    end

    hott def left (G : Pregroup) [Algebra.group G] (x : G.carrier) : G.carrier ≃ G.carrier :=
    begin
      existsi (G.φ x ·); apply Prod.mk <;> existsi (G.φ (G.ι x) ·) <;> intro y;
      { transitivity; { symmetry; apply G.mulAssoc };
        transitivity; { apply Id.map (G.φ · y); apply G.mulLeftInv };
        apply G.oneMul };
      { transitivity; { symmetry; apply G.mulAssoc };
        transitivity; { apply Id.map (G.φ · y); apply mulRightInv };
        apply G.oneMul }
    end

    hott def S.univ (G : Pregroup.{u}) [Algebra.group G] : G ⤳ S G.zero :=
    mkhomo (left G)
      (begin
        intros x y; fapply Theorems.Prop.equivHmtpyLem;
        intro; apply G.mulAssoc
      end)

    hott def S.univ.ker.encode : (ker (S.univ G)).set ⊆ (triv G).set :=
    begin
      intro x H; change _ = _; symmetry;
      apply unitOfSqr; apply Equiv.happlyEqv H
    end

    hott def S.univ.ker.decode : (triv G).set ⊆ (ker (S.univ G)).set :=
    begin
      intros x H; apply Theorems.Prop.equivHmtpyLem;
      intro y; induction H using Id.casesOn; apply G.oneMul
    end

    noncomputable hott def S.univ.ker : ker (S.univ G) = triv G :=
    subgroup.ext (Ens.ssubset.asymm S.univ.ker.encode S.univ.ker.decode)
  end
end Group

end GroundZero.Algebra