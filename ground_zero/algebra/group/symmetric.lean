import ground_zero.algebra.group.subgroup
open ground_zero.structures
open ground_zero.types
open ground_zero.proto
open ground_zero

/-
  Symmetric group.
  * https://en.wikipedia.org/wiki/Symmetric_group
-/

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  open ground_zero.algebra.pregroup (right_div left_div conjugate conjugate_rev subgroup)

  variables {G : pregroup} [group G]
  local infix ` * `  := G.φ
  local notation `e` := G.e
  local postfix ⁻¹   := G.ι

  -- Permutations
  @[hott] def S.carrier (ε : 0-Type) := ε ≃₀ ε

  section
    variables {ε : 0-Type}
    @[hott] def S.mul (p q : S.carrier ε) := equiv.trans q p
    @[hott] def S.one                     := equiv.id ε.fst
    @[hott] def S.inv (p : S.carrier ε)   := equiv.symm p

    @[hott] instance S.has_mul : has_mul (S.carrier ε) := ⟨S.mul⟩
    @[hott] instance S.has_one : has_one (S.carrier ε) := ⟨S.one⟩
    @[hott] instance S.has_inv : has_inv (S.carrier ε) := ⟨S.inv⟩

    section
      include ε
      @[hott] def S (ε : n_type.{u} 0) : pregroup.{u} :=
      @pregroup.intro (ε ≃₀ ε) (λ _ _, theorems.prop.zeroequiv.hset ε ε) S.mul S.inv S.one

      @[hott] instance S.semigroup : semigroup (S ε).magma :=
      ⟨begin
        intros, fapply theorems.prop.equiv_hmtpy_lem,
        intro x, induction a, induction b, induction c, reflexivity
      end⟩

      @[hott] instance S.monoid : monoid (S ε).premonoid :=
      begin
        split, exact S.semigroup,
        repeat { intro x, fapply theorems.prop.equiv_hmtpy_lem,
                 intro y, induction x, reflexivity },
      end

      @[hott] instance S.group : group (S ε) :=
      begin
        split, exact S.monoid, intro x,
        fapply theorems.prop.equiv_hmtpy_lem, intro y,
        induction x with f x, induction x with e₁ e₂,
        induction e₁ with g p, induction e₂ with h q,
        change h _ = y, apply qinv.linv_inv, exact q, exact p
      end
    end

    @[hott] def left (G : pregroup) [group G] (x : G.carrier) : G.carrier ≃ G.carrier :=
    begin
      existsi (λ y, x * y), split; existsi (λ y, x⁻¹ * y); intro y,
      { transitivity, { symmetry, apply G.mul_assoc },
        transitivity, { apply Id.map (* y), apply G.mul_left_inv },
        apply G.one_mul },
      { transitivity, { symmetry, apply G.mul_assoc },
        transitivity, { apply Id.map (* y), apply mul_right_inv },
        apply G.one_mul }
    end

    @[hott] def S.univ (G : pregroup.{u}) [group G] : G ⤳ S G.zero :=
    mkhomo (left G)
      (begin
        intros x y, fapply theorems.prop.equiv_hmtpy_lem,
        intro z, apply G.mul_assoc
      end)

    @[hott] def S.univ.ker.encode : ker (S.univ G) ⊆ triv G :=
    begin
      intros x H, change _ = _,
      symmetry, apply unit_of_sqr, apply equiv.happly H
    end

    @[hott] def S.univ.ker.decode : triv G ⊆ ker (S.univ G) :=
    begin
      intros x H, apply theorems.prop.equiv_hmtpy_lem,
      intro y, induction H, apply G.one_mul
    end

    @[hott] noncomputable def S.univ.ker : ker (S.univ G) = triv G :=
    subgroup.ext (ens.ssubset.asymm S.univ.ker.encode S.univ.ker.decode)
  end
end group

end ground_zero.algebra