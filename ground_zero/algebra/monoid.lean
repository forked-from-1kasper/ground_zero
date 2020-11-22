import ground_zero.algebra.basic
import ground_zero.HITs.trunc
open ground_zero ground_zero.types

hott theory

namespace ground_zero.algebra

universes u v

namespace monoid
  variables {M N : monoid}

  @[hott] def respects_mul (ψ : M.carrier → N.carrier) :=
  Π a b, ψ (M.φ a b) = N.φ (ψ a) (ψ b)

  @[hott] def homo (M N : monoid) :=
  Σ (φ : M.carrier → N.carrier), φ M.e = N.e × respects_mul φ

  infix ` ⤳ `:20 := homo

  meta def setpi :=
  `[ intros, repeat { apply structures.pi_respects_ntype 0, intros },
     apply structures.hlevel.cumulative 0, apply HITs.trunc.uniq 0 ]

  meta def indtrunc :=
  `[ intro x, fapply HITs.trunc.ind _ _ x; clear x ]

  @[hott] noncomputable def F.semigroup (ε : Type u) : semigroup :=
  ⟨⟨⟨∥list ε∥₀, HITs.trunc.uniq 0⟩, HITs.trunc.lift₂ list.append⟩,
    begin
      indtrunc, intro a,
      indtrunc, intro b,
      indtrunc, intro c,
      apply Id.map HITs.trunc.elem,
      { induction a; induction b; induction c; try { reflexivity },
        repeat { apply Id.map (list.cons _), assumption } },
      iterate 3 { setpi }
    end⟩

  @[hott] noncomputable def F (ε : Type u) : monoid :=
  ⟨F.semigroup ε, HITs.trunc.elem [],
  begin
    indtrunc, intro a,
    apply Id.map HITs.trunc.elem,
    reflexivity, setpi
  end, begin
    indtrunc, intro a,
    apply Id.map HITs.trunc.elem,
    induction a,
    { reflexivity },
    { apply Id.map (list.cons _),
      assumption },
    setpi
  end⟩

  @[hott] noncomputable def F.homomorphism {ε : Type v}
    {M : monoid} (φ : ε → M.carrier) : F ε ⤳ M :=
  ⟨HITs.trunc.rec (list.foldr (M.φ ∘ φ) M.e) M.α.snd, by reflexivity,
  begin
    indtrunc, intro a,
    indtrunc, intro b,
    { induction a,
      { transitivity, apply M.one_mul, } },
    repeat {
      intro x, try { apply structures.pi_respects_ntype 0, intro y },
      apply structures.hlevel.cumulative 0, exact M.α.snd
    }
  end⟩
end monoid

end ground_zero.algebra