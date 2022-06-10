import GroundZero.Algebra.Group.Basic
open GroundZero.Types

namespace GroundZero.Algebra

namespace Group
  hott def Prod (G H : Group) : Group :=
  @Group.intro (G.carrier × H.carrier)
    (GroundZero.Structures.prodHset G.hset H.hset)
    (λ w₁ w₂, (G.φ w₁.1 w₂.1, H.φ w₁.2 w₂.2))
    (λ w, (G.ι w.1, H.ι w.2)) (G.e, H.e)
    (λ _ _ _, Product.prod (G.mulAssoc _ _ _) (H.mulAssoc _ _ _))
    (λ _, Product.prod (G.oneMul _) (H.oneMul _))
    (λ _, Product.prod (G.mulOne _) (H.mulOne _))
    (λ _, Product.prod (G.mulLeftInv _) (H.mulLeftInv _))

  infixl:70 " × " => Prod

  hott def Prod.abelian (G H : Group)
    (ρ₁ : G.isCommutative) (ρ₂ : H.isCommutative) : (G × H).isCommutative :=
  λ _ _, Product.prod (ρ₁ _ _) (ρ₂ _ _)

  hott def Homo.prod {G H F : Group} (ρ : F.isCommutative)
    (φ : Hom G F) (ψ : Hom H F) : Hom (G × H) F :=
  begin
    fapply mkhomo; exact (λ w, F.φ (φ.1 w.1) (ψ.1 w.2)); intros x y;
    change F.φ (φ.1 _) (ψ.1 _) = F.φ (F.φ _ _) (F.φ _ _);
    transitivity; apply Equiv.bimap F.φ <;> apply homoMul;
    transitivity; apply F.mulAssoc;
    transitivity; apply Id.map (F.φ (φ.1 _));
    transitivity; apply ρ; apply F.mulAssoc;
    transitivity; symmetry; apply F.mulAssoc;
    apply Id.map; apply ρ
  end
end Group

end GroundZero.Algebra