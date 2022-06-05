import GroundZero.Algebra.Group.Basic
open GroundZero.Types

namespace GroundZero.Algebra

namespace Group
  hott def Prod (G H : Pregroup) : Pregroup :=
  @Pregroup.intro (G.carrier × H.carrier)
    (GroundZero.Structures.prodHset G.hset H.hset)
    (λ w₁ w₂, (G.φ w₁.1 w₂.1, H.φ w₁.2 w₂.2))
    (λ w, (G.ι w.1, H.ι w.2))
    (G.e, H.e)
  infix:70 " × " => Prod

  section
    variable {G H : Pregroup} [group G] [group H]

    instance Prod.semigroup : semigroup (G × H).magma :=
    ⟨begin intros a b c; apply Product.prod; apply G.mulAssoc; apply H.mulAssoc end⟩

    instance Prod.monoid : monoid (G × H).premonoid :=
    ⟨Prod.semigroup, begin
      intro a; apply Product.prod;
      apply G.oneMul; apply H.oneMul
    end,
    begin
      intro a; apply Product.prod;
      apply G.mulOne; apply H.mulOne
    end⟩

    instance Prod.group : group (G × H) :=
    ⟨Prod.monoid, begin
      intros a; apply Product.prod;
      apply G.mulLeftInv; apply H.mulLeftInv
    end⟩
  end

  instance Prod.abelian (G H : Pregroup)
    [abelian G] [abelian H] : abelian (G × H) :=
  begin constructor; intro x y; apply Product.prod <;> apply abelian.mulComm end

  hott def Homo.prod {G H F : Pregroup} [group G] [group H] [abelian F]
    (φ : G ⤳ F) (ψ : H ⤳ F) : (G × H) ⤳ F :=
  begin
    fapply mkhomo; exact (λ w, F.φ (φ.1 w.1) (ψ.1 w.2)); intros x y;
    change F.φ (φ.1 _) (ψ.1 _) = F.φ (F.φ _ _) (F.φ _ _);
    transitivity; apply Equiv.bimap F.φ <;> apply homoMul;
    transitivity; apply F.mulAssoc;
    transitivity; apply Id.map (F.φ (φ.1 _));
    transitivity; apply abelian.mulComm; apply F.mulAssoc;
    transitivity; symmetry; apply F.mulAssoc;
    apply Id.map; apply abelian.mulComm
  end
end Group

end GroundZero.Algebra