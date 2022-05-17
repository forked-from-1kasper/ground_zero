import ground_zero.algebra.group.automorphism
open ground_zero.structures
open ground_zero.types
open ground_zero

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  -- Outer semidirect product
  @[hott] def semidirect {N H : pregroup}
    [group N] [group H] (φ : H ⤳ Aut N) : pregroup :=
  @pregroup.intro (N.carrier × H.carrier)
    (λ _ _, prod_hset (λ _ _, N.hset) (λ _ _, H.hset))
    (λ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩, (N.φ n₁ ((φ.fst h₁).fst n₂), H.φ h₁ h₂))
    (λ ⟨n, h⟩, ⟨(φ.fst (H.ι h)).fst (N.ι n), H.ι h⟩) (N.e, H.e)

  notation N ` ⋊` `[` φ `] ` H := @semidirect N H _ _ φ
  notation H ` ⋉` `[` φ `] ` N := @semidirect N H _ _ φ

  section
    variables {N H : pregroup} [group N] [group H] (φ : H ⤳ Aut N)

    @[hott] noncomputable instance semidirect.semigroup : semigroup (N ⋊[φ] H).magma :=
    ⟨λ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩ ⟨n₃, h₃⟩, begin
      apply product.prod,
      { repeat { clear _fun_match },
        induction φ with φ p,
        transitivity, apply N.mul_assoc,
        apply Id.map (N.φ n₁), symmetry,
        transitivity, apply iso_mul,
        apply Id.map, symmetry,
        transitivity, apply HITs.interval.happly,
        apply Id.map, apply homo_mul, reflexivity },
      { apply H.mul_assoc }
    end⟩

    @[hott] noncomputable instance semidirect.monoid : monoid (N ⋊[φ] H).premonoid :=
    ⟨semidirect.semigroup φ, λ ⟨n, h⟩, begin
      apply product.prod,
      { transitivity, apply N.one_mul,
        transitivity, apply HITs.interval.happly,
        apply Id.map, apply homo_unit, reflexivity },
      { apply H.one_mul }
    end, λ ⟨n, h⟩, begin
      apply product.prod,
      { transitivity, apply Id.map (N.φ n),
        apply iso_unit (φ.fst h), apply N.mul_one },
      { apply H.mul_one }
    end⟩

    @[hott] noncomputable instance semidirect.group : group (N ⋊[φ] H) :=
    ⟨semidirect.monoid φ,
    λ ⟨n, h⟩, begin
      apply product.prod,
      { transitivity, symmetry, apply iso_mul,
        transitivity, apply Id.map, apply N.mul_left_inv,
        apply iso_unit },
      { apply H.mul_left_inv }
    end⟩
  end
end group

end ground_zero.algebra