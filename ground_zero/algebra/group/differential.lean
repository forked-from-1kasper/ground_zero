import ground_zero.algebra.group.subgroup
open ground_zero.structures
open ground_zero.types
open ground_zero.proto
open ground_zero

/-
  Differential group.
  * https://encyclopediaofmath.org/wiki/Differential_group
-/

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  variables {G : pregroup} [group G]

  @[hott] def im_impl_ker {φ : G ⤳ G}
    (H : φ ⋅ φ = 0) : im φ ⊆ ker φ :=
  begin
    intro x, fapply HITs.merely.rec, { apply G.hset },
    { intro H, induction H with y p, change _ = _,
      transitivity, apply Id.map, exact Id.inv p,
      apply @idhomo _ _ _ _ _ (φ ⋅ φ) 0, apply H }
  end

  @[hott] noncomputable def boundary_of_boundary {φ : G ⤳ G}
    (p : im φ ⊆ ker φ) : φ ⋅ φ = 0 :=
  begin
    induction φ with φ H, fapply homo.funext,
    intro x, apply p, apply HITs.merely.elem,
    existsi x, trivial
  end

  @[hott] noncomputable def boundary_eqv (φ : G ⤳ G) :
    (φ ⋅ φ = 0) ≃ (im φ ⊆ ker φ) :=
  begin
    apply structures.prop_equiv_lemma,
    apply homo.set, apply ens.ssubset.prop,
    exact im_impl_ker, exact boundary_of_boundary
  end

end group

def diff := Σ (G : pregroup) [H : abelian G] (δ : G ⤳ G),
  δ ⋅ δ = @group.homo.zero G H.to_group G H.to_group

-- Accessors
def diff.grp (G : diff) := G.fst
instance diff.abelian (G : diff) : abelian G.grp := G.snd.fst

def diff.δ   (G : diff) : G.grp ⤳ G.grp := G.snd.snd.fst
def diff.sqr (G : diff) : G.δ ⋅ G.δ = 0 := G.snd.snd.snd

namespace diff
  open ground_zero.algebra.group (im ker)
  variables (G : diff)

  @[hott] def univ : group.im G.δ ⊆ ker G.δ :=
  group.im_impl_ker G.sqr
end diff

end ground_zero.algebra