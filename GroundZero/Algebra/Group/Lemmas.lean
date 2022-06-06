import GroundZero.Algebra.Group.Subgroup
import GroundZero.Theorems.Nat

open GroundZero.Types.Equiv (transport)
open GroundZero.Theorems
open GroundZero.Types
open GroundZero

namespace GroundZero.Algebra

namespace Group
  variable {G : Pregroup} [group G]

  local infixl:70 (priority := high) " * " => G.φ
  local postfix:max (priority := high) "⁻¹" => G.ι
  local notation "e" => G.e

  hott def union (φ : ℕ → G.subgroup) (p : Π i, (φ i).set ⊆ (φ (i + 1)).set) : G.subgroup :=
  begin
    fapply Pregroup.subgroup.mk; exact ⋃(λ n, (φ n).set);
    { apply HITs.Merely.elem; existsi 0; apply (φ 0).unit };
    { intros a b; apply HITs.Merely.lift₂; intro ⟨n, r⟩ ⟨m, s⟩;
      let ε := @Nat.le.elim (λ n m, (φ n).set ⊆ (φ m).set)
        (λ n m k, Ens.ssubset.trans)
        (λ n, Ens.ssubset.refl (φ n).set) p;
      existsi Theorems.Nat.max n m; apply (φ _).mul;
      apply ε; apply Nat.le.max; assumption;
      apply ε; apply Nat.le.maxRev; assumption };
    { intro a; apply HITs.Merely.lift; intro ⟨n, r⟩;
      existsi n; apply (φ n).inv; assumption }
  end

  hott def distinctNormalSubgroups {φ ψ : G.subgroup}
    (H : Π x, x ∈ φ.set → x ∈ ψ.set → x = e) [G ⊵ φ] [G ⊵ ψ] :
    Π g h, g ∈ φ.set → h ∈ ψ.set → g * h = h * g :=
  begin
    intros g h p q; apply commutes; apply H;
    { apply transport (· ∈ φ.set); symmetry;
      apply G.mulAssoc; apply φ.mul; exact p;
      apply transport (· ∈ φ.set); apply G.mulAssoc;
      apply conjugateEqv; apply isNormalSubgroup.conj;
      apply φ.inv; exact p };
    { apply transport (· ∈ ψ.set); apply G.mulAssoc;
      apply ψ.mul; apply conjugateEqv;
      apply isNormalSubgroup.conj; exact q;
      apply ψ.inv; exact q }
  end
end Group

end GroundZero.Algebra