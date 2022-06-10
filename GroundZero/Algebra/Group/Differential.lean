import GroundZero.Algebra.Group.Subgroup
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero

/-
  Differential group.
  * https://encyclopediaofmath.org/wiki/Differential_group
-/

namespace GroundZero.Algebra
universe u v u' v' w

namespace Group
  variable {G : Group}

  hott def imImplKer {φ : Hom G G} (H : φ ⋅ φ = 0) : (im φ).set ⊆ (ker φ).set :=
  begin
    intro x; fapply HITs.Merely.rec; apply G.hset;
    intro ⟨y, p⟩; change _ = _; transitivity; apply Id.map _ (Id.inv p);
    apply @idhom _ _ _ _ _ (φ ⋅ φ) 0; apply H
  end

  noncomputable hott def boundaryOfBoundary {φ : Hom G G}
    (p : (im φ).set ⊆ (ker φ).set) : φ ⋅ φ = 0 :=
  begin
    fapply Hom.funext; intro x; apply p;
    apply HITs.Merely.elem; existsi x; reflexivity
  end

  noncomputable hott def boundaryEqv (φ : Hom G G) :
    (φ ⋅ φ = 0) ≃ ((im φ).set ⊆ (ker φ).set) :=
  begin
    apply Structures.propEquivLemma;
    apply Homo.set; apply Ens.ssubset.prop;
    exact imImplKer; exact boundaryOfBoundary
  end
end Group

def Diff := Σ (G : Abelian) (δ : Abelian.Hom G G), δ ⋅ δ = 0

-- Accessors
hott def Diff.abelian (G : Diff) := G.1
hott def Diff.group (G : Diff) := G.abelian.group

hott def Diff.δ   (G : Diff) : Group.Hom G.group G.group := G.2.1
hott def Diff.sqr (G : Diff) : G.δ ⋅ G.δ = 0 := G.2.2

namespace Diff
  open GroundZero.Algebra.Group (ker)
  variable (G : Diff)

  hott def univ : (Group.im G.δ).set ⊆ (ker G.δ).set :=
  Group.imImplKer G.sqr
end Diff

end GroundZero.Algebra