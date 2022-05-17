import ground_zero.algebra.group.basic
open ground_zero.types

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  @[hott] def prod (G H : pregroup) : pregroup :=
  @pregroup.intro (G.carrier × H.carrier)
    (λ _ _, ground_zero.structures.prod_hset (λ _ _, G.hset) (λ _ _, H.hset))
    (λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩, (G.φ a₁ a₂, H.φ b₁ b₂))
    (λ ⟨a, b⟩, (G.ι a, H.ι b)) (G.e, H.e)
  notation G × H := prod G H

  section
    variables {G H : pregroup} [group G] [group H]

    @[hott] instance prod.semigroup : semigroup (G × H).magma :=
    ⟨begin
      intros a b c, cases a, cases b, cases c,
      apply product.prod, apply G.mul_assoc, apply H.mul_assoc
    end⟩

    @[hott] instance prod.monoid : monoid (G × H).premonoid :=
    ⟨prod.semigroup, begin
      intros a, cases a, apply product.prod,
      apply G.one_mul, apply H.one_mul
    end,
    begin
      intros a, cases a, apply product.prod,
      apply G.mul_one, apply H.mul_one
    end⟩

    @[hott] instance prod.group : group (G × H) :=
    ⟨prod.monoid, begin
      intros a, cases a, apply product.prod,
      apply G.mul_left_inv, apply H.mul_left_inv
    end⟩
  end

  @[hott] instance prod.abelian (G H : pregroup)
    [abelian G] [abelian H] : abelian (G × H) :=
  begin
    split, intros x y, cases x, cases y,
    apply product.prod; apply abelian.mul_comm
  end

  @[hott] def homo.prod {G H F : pregroup} [group G] [group H] [abelian F]
    (φ : G ⤳ F) (ψ : H ⤳ F) : G × H ⤳ F :=
  begin
    fapply mkhomo, exact (λ ⟨g, h⟩, F.φ (φ.fst g) (ψ.fst h)),
    intros x y, cases x with g₁ h₁, cases y with g₂ h₂,
    change F.φ (φ.fst _) (ψ.fst _) = F.φ (F.φ _ _) (F.φ _ _),
    transitivity, apply equiv.bimap F.φ; apply homo_mul,
    transitivity, apply F.mul_assoc,
    transitivity, apply Id.map (F.φ (φ.fst g₁)),
    transitivity, apply abelian.mul_comm, apply F.mul_assoc,
    transitivity, symmetry, apply F.mul_assoc,
    apply Id.map, apply abelian.mul_comm
  end
end group

end ground_zero.algebra