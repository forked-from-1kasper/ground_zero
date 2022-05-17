import ground_zero.HITs.quotient ground_zero.algebra.group.basic
open ground_zero.types
open ground_zero

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  variables {G : pregroup} [group G]

  @[hott] def «Sosnitsky construction» (G : pregroup) [group G] :=
  @HITs.quotient G.carrier
    ⟨λ g h, ⟨∥(g = h) + (g = G.ι h)∥, HITs.merely.uniq⟩, begin
      split, intro a, apply HITs.merely.elem, left, reflexivity, split,
      { intros a b, apply HITs.merely.lift, intro p,
        induction p with u v, left, exact Id.inv u,
        right, transitivity, symmetry, apply inv_inv,
        apply Id.map, exact Id.inv v },
      { intros a b c, apply HITs.merely.lift₂, intros p q,
        induction p with p₁ p₂; induction q with q₁ q₂,
        { left, exact Id.trans p₁ q₁ },
        { right, exact Id.trans p₁ q₂ },
        { right, transitivity, exact p₂,
          apply Id.map, exact q₁ },
        { left, transitivity, exact p₂, transitivity,
          apply Id.map, exact q₂, apply inv_inv } }
    end⟩

  notation `⌈` G `⌉` := «Sosnitsky construction» G

  def absolutizer (G : pregroup.{u}) [group G] :=
  Σ (φ : ⌈G⌉ → G.carrier), φ ∘ HITs.quotient.elem ∘ φ ~ φ

  section
    variable (φ : absolutizer G)
    def absolutizer.ap := φ.fst ∘ HITs.quotient.elem

    @[hott] def absolutizer.idem : φ.ap ∘ φ.ap ~ φ.ap :=
    λ x, φ.snd (HITs.quotient.elem x)

    @[hott] def absolutizer.even : φ.ap ∘ G.ι ~ φ.ap :=
    begin
      intro x, apply Id.map φ.fst, apply HITs.quotient.sound,
      apply HITs.merely.elem, right, reflexivity
    end

    @[hott] def absolutizer.inv : absolutizer G :=
    ⟨G.ι ∘ φ.fst, begin
      intro x, apply Id.map G.ι,
      transitivity, apply φ.even, apply φ.snd
    end⟩

    @[hott] def absolutizer.comp₁ : φ.ap ∘ φ.inv.ap ~ φ.ap :=
    begin intro x, transitivity, apply φ.even, apply φ.idem end

    @[hott] def absolutizer.comp₂ : φ.inv.ap ∘ φ.ap ~ φ.inv.ap :=
    begin intro x, apply Id.map G.ι, apply φ.idem end

    include φ
    @[hott] noncomputable def absolutizer.mul : ⌈G⌉ → ⌈G⌉ → ⌈G⌉ :=
    begin
      fapply HITs.quotient.lift₂,
      { intros a b, apply HITs.quotient.elem, exact G.φ (φ.ap a) (φ.ap b) },
      { apply HITs.quotient.set },
      { intros a₁ a₂ b₁ b₂, intro p, fapply HITs.merely.rec _ _ p; clear p,
        { apply structures.pi_prop, intro x, apply HITs.quotient.set },
        { intro p, fapply HITs.merely.rec, apply HITs.quotient.set,
          intro q, fapply Id.map HITs.quotient.elem, fapply equiv.bimap,
          { induction p, exact φ.ap # p,
            transitivity, apply φ.ap # p,
            apply absolutizer.even },
          { induction q, exact φ.ap # q,
            transitivity, apply φ.ap # q,
            apply absolutizer.even } } }
    end

    omit φ
    @[hott] def absolutizer.one : ⌈G⌉ :=
    HITs.quotient.elem G.e
  end
end group

end ground_zero.algebra