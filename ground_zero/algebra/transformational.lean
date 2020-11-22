import ground_zero.algebra.group
open ground_zero.algebra.group (S S.ap orbit Orbits)
open ground_zero.types.equiv
open ground_zero.structures
open ground_zero.types
open ground_zero.HITs
open ground_zero

hott theory

universes u v

namespace ground_zero.algebra
  -- Generalized Interval System and Its Applications, Minseon Song
  -- https://www.whitman.edu/documents/Academics/Mathematics/2014/songm.pdf
  structure gis (M : Type u) (G : group) :=
  (ι     : M → M → G.carrier)
  (trans : Π x y z, G.φ (ι x y) (ι y z) = ι x z)
  (full  : Π g x, contr (Σ y, ι x y = g))

  namespace gis
    variables {M : Type u} {G : group} (L : gis M G)
    include L

    local infix ` * ` := G.φ
    local postfix ⁻¹ := G.inv

    @[hott] def neut : Π x, L.ι x x = G.e :=
    begin intro x, apply group.unit_of_sqr, apply L.trans end

    @[hott] def inv : Π x y, (L.ι x y)⁻¹ = L.ι y x :=
    begin
      intros x y, apply group.inv_eq_of_mul_eq_one,
      transitivity, apply L.trans, apply gis.neut
    end

    @[hott] def propι : Π g x, prop (Σ y, L.ι x y = g) :=
    λ g x, contr_impl_prop (L.full g x)

    @[hott] def fixι : Π g x, Σ y, L.ι x y = g :=
    λ g x, (L.full g x).point

    @[hott] def zero {x y : M} : L.ι x y = G.e → x = y :=
    begin
      intro p, symmetry,
      have r := L.propι (L.ι x y) x ⟨y, Id.refl⟩ ⟨x, L.neut x ⬝ Id.inv p⟩,
      apply Id.map sigma.fst r
    end

    @[hott] def injιᵣ {x y z : M} : L.ι z x = L.ι z y → x = y :=
    begin
      intro p, apply L.zero,
      transitivity, symmetry, apply L.trans x z y,
      transitivity, apply Id.map, exact Id.inv p,
      transitivity, apply L.trans, apply neut
    end

    @[hott] def injιₗ {x y z : M} : L.ι x z = L.ι y z → x = y :=
    begin
      intro p, apply L.injιᵣ, apply group.inv_inj,
      transitivity, apply inv, symmetry,
      transitivity, apply inv,
      exact Id.inv p
    end

    omit L
    @[hott] def prod {M₁ : Type u} {M₂ : Type v} {G H : group} :
      gis M₁ G → gis M₂ H → gis (M₁ × M₂) (G × H) :=
    begin
      intros L K, fapply gis.mk,
      { intros m₁ m₂, fapply prod.intro,
        exact L.ι m₁.fst m₂.fst,
        exact K.ι m₁.snd m₂.snd },
      { intros x y z, fapply product.prod,
        apply L.trans, apply K.trans },
      { intros g x, induction g with g₁ g₂, fapply contr.mk,
        { fapply sigma.mk,
          { fapply prod.intro,
            exact (L.fixι g₁ x.fst).fst,
            exact (K.fixι g₂ x.snd).fst },
          fapply product.prod,
          { apply (L.fixι g₁ x.fst).snd },
          { apply (K.fixι g₂ x.snd).snd } },
        { intro p, induction p with p v,
          induction p with p₁ p₂, fapply sigma.prod,
          { fapply product.prod,
            apply Id.map sigma.fst ((L.full g₁ x.fst).intro ⟨p₁, Id.map prod.fst v⟩),
            apply Id.map sigma.fst ((K.full g₂ x.snd).intro ⟨p₂, Id.map prod.snd v⟩) },
          { apply group.prod_hset; intros p q,
            apply G.set, apply H.set } } }
    end
    notation L × K := prod L K

    @[hott] def octave.hrel (φ : G.subset) : hrel M :=
    λ a b, ⟨L.ι a b ∈ φ, ens.prop _ φ⟩

    include L
    @[hott] def octave (φ : G.subset) [G ≥ φ] : eqrel M :=
    begin
      existsi octave.hrel L φ, split,
      { intro a, apply transport (∈ φ),
        exact Id.inv (L.neut a),
        apply group.is_subgroup.unit }, split,
      { intros a b p, apply transport (∈ φ),
        apply L.inv, apply group.is_subgroup.inv,
        exact p },
      { intros a b c p q, apply transport (∈ φ),
        apply L.trans a b c, apply group.is_subgroup.mul;
        assumption }
    end

    -- Transposition
    @[hott] def τ (i : G.carrier) : M → M :=
    λ x, (L.fixι i x).fst

    @[hott] def τ.lawful : Π i x, L.ι x (L.τ i x) = i :=
    λ i x, (L.fixι i x).snd
  end gis

  -- In case of α = {C, C♯, D, D♯, E, F, ...},
  -- this is 12 ordered notes
  abbreviation P (α : 0-Type) := α ≃₀ α

  def L (α : Type u) := Σ n, finite n → α

  def L.length {α : Type u} : L α → ℕ := sigma.fst
  def L.nth {α : Type u} (xs : L α) : finite xs.length → α := xs.snd

  @[hott] def L.all {α : Type u} (π : α → propset)
    (xs : L α) : propset :=
  ⟨Π n, (π (xs.nth n)).fst, begin
    apply pi_prop, intro x,
    apply (π _).snd
  end⟩

  -- Set of (12 × n) ordered notes, where n ∈ ℕ
  def M (α : 0-Type) := L (P α).fst

  -- Set of *all* tone row transformations
  abbreviation T (α : 0-Type) := S (P α)

  section
    variables {α : 0-Type} (φ : (T α).subset) [T α ≥ φ]

    -- Tone row transformations in terms of φ ≤ T α
    def tr := (@S.ap (α ≃₀ α)).cut φ

    -- Set of tone rows
    def R := Orbits (tr φ)

    def M.dodecaphonic (xs : M α) (r : (P α).fst) : propset :=
    xs.all (λ x, ⟨x ∈ orbit (tr φ) r, ens.prop _ _⟩)
  end
end ground_zero.algebra