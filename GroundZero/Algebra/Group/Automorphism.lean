import GroundZero.Algebra.Group.Basic

namespace GroundZero.Algebra

namespace Group
  def Aut.carrier (G : Pregroup) := G ≅ G

  noncomputable hott def Aut (G : Pregroup) : Pregroup :=
  @Pregroup.intro (G ≅ G) Iso.hset (λ φ ψ, Iso.trans ψ φ) Iso.symm (Iso.refl G)

  macro "isoFunext" : tactic => `(apply Iso.ext; intro; reflexivity)

  variable {G : Pregroup} [group G]

  noncomputable instance Aut.semigroup : semigroup (Aut G).magma :=
  ⟨λ ⟨f, ⟨f', e₁⟩⟩ ⟨g, ⟨g', e₂⟩⟩ ⟨h, ⟨h', e₂⟩⟩, by isoFunext⟩

  noncomputable instance Aut.monoid : monoid (Aut G).premonoid :=
  ⟨Aut.semigroup,
   λ ⟨f, ⟨f', e₁⟩⟩, by isoFunext,
   λ ⟨f, ⟨f', e₁⟩⟩, by isoFunext⟩

  noncomputable instance Aut.group : group (Aut G) :=
  ⟨Aut.monoid, λ ⟨f, ⟨(η₁, η₂), (⟨g, μ₁⟩, μ₂)⟩⟩,
   begin apply Iso.ext; apply μ₁ end⟩
end Group

end GroundZero.Algebra