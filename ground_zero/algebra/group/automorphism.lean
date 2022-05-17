import ground_zero.algebra.group.basic

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  def Aut.carrier (G : pregroup) := G ≅ G

  @[hott] noncomputable def Aut (G : pregroup) : pregroup :=
  @pregroup.intro (G ≅ G) (λ _ _, iso.hset)
    (λ φ ψ, iso.trans ψ φ) iso.symm (iso.refl G)

  meta def iso.funext :=
  `[ apply iso.ext, intro x, reflexivity ]

  variables {G : pregroup} [group G]

  @[hott] noncomputable instance Aut.semigroup : semigroup (Aut G).magma :=
  ⟨λ ⟨f, ⟨f', e₁⟩⟩ ⟨g, ⟨g', e₂⟩⟩ ⟨h, ⟨h', e₂⟩⟩, by iso.funext⟩

  @[hott] noncomputable instance Aut.monoid : monoid (Aut G).premonoid :=
  ⟨Aut.semigroup,
   λ ⟨f, ⟨f', e₁⟩⟩, by iso.funext,
   λ ⟨f, ⟨f', e₁⟩⟩, by iso.funext⟩

  @[hott] noncomputable instance Aut.group : group (Aut G) :=
  ⟨Aut.monoid, λ ⟨f, ⟨(η₁, η₂), (⟨g, μ₁⟩, μ₂)⟩⟩, begin
    apply iso.ext, apply μ₁
  end⟩
end group

end ground_zero.algebra