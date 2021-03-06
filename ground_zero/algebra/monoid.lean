import ground_zero.algebra.basic
import ground_zero.HITs.trunc
open ground_zero ground_zero.types

hott theory

namespace ground_zero.algebra

universes u v

namespace monoid
  variables {M N : premonoid}

  meta def setpi :=
  `[ intros, repeat { apply structures.pi_respects_ntype 0, intros },
     apply structures.hlevel.cumulative 0, apply HITs.trunc.uniq 0 ]

  meta def indtrunc :=
  `[ intro x, fapply HITs.trunc.ind _ _ x; clear x ]

  @[hott] noncomputable def F.carrier (ε : Type u) : 0-Type :=
  ⟨∥list ε∥₀, HITs.trunc.uniq 0⟩

  @[hott] noncomputable def F (ε : Type u) : premonoid :=
  begin
    existsi (F.carrier ε), split; intro i; induction i; intro v,
    { induction v, exact HITs.trunc.elem [] },
    { induction v with x v, induction v with y v,
      exact HITs.trunc.lift₂ list.append x y }
  end

  @[hott] noncomputable def F.semigroup (ε : Type u) : semigroup (F ε).magma :=
  ⟨begin
    indtrunc, intro a,
    indtrunc, intro b,
    indtrunc, intro c,
    apply Id.map HITs.trunc.elem,
    { induction a; induction b; induction c; try { reflexivity },
      repeat { apply Id.map (list.cons _), assumption } },
    iterate 3 { setpi }
  end⟩

  @[hott] noncomputable def F.monoid (ε : Type u) : monoid (F ε) :=
  ⟨F.semigroup ε,
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
end monoid

end ground_zero.algebra