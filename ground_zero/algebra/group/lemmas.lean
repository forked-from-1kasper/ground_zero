import ground_zero.algebra.group.subgroup ground_zero.theorems.nat
open ground_zero.types.equiv (transport)
open ground_zero.theorems
open ground_zero.types
open ground_zero

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  variables {G : pregroup} [group G]
  local infix ` * `  := G.φ
  local notation `e` := G.e
  local postfix ⁻¹   := G.ι

  @[hott] def union (φ : ℕ → G.subgroup) (p : Π i, φ i ⊆ φ (i + 1)) : G.subgroup :=
  begin
    fapply pregroup.subgroup.mk, exact ⋃(λ n, (φ n).set),
    { apply HITs.merely.elem, existsi 0, apply (φ 0).unit },
    { intros a b, apply HITs.merely.lift₂,
      intros r s, induction r with n r, induction s with m s,
      let ε := @nat.le.elim (λ n m, φ n ⊆ φ m)
        (λ n m k, ens.ssubset.trans) (λ n, ens.ssubset.refl (φ n).set) p,
      existsi nat.max n m, apply (φ (nat.max n m)).mul,
      apply ε, apply nat.le.max, assumption,
      apply ε, apply nat.le.max_rev, assumption },
    { intro a, apply HITs.merely.lift, intro r,
      induction r with n r, existsi n, apply (φ n).inv,
      assumption }
  end

  @[hott] def distinct_normal_subgroups {φ ψ : G.subgroup}
    (H : Π x, x ∈ φ → x ∈ ψ → x = e) [G ⊵ φ] [G ⊵ ψ] :
    Π g h, g ∈ φ → h ∈ ψ → g * h = h * g :=
  begin
    intros g h p q, apply commutes, apply H,
    { apply transport (∈ φ), symmetry,
      apply G.mul_assoc, apply φ.mul, exact p,
      apply transport (∈ φ), apply G.mul_assoc,
      apply conjugate_eqv, apply is_normal_subgroup.conj,
      apply φ.inv, exact p },
    { apply transport (∈ ψ), apply G.mul_assoc,
      apply ψ.mul, apply conjugate_eqv,
      apply is_normal_subgroup.conj, exact q,
      apply ψ.inv, exact q }
  end
end group

end ground_zero.algebra