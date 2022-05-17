import ground_zero.algebra.reals ground_zero.algebra.group.symmetric
open ground_zero.HITs (merely merely.uniq merely.elem merely.rec merely.lift)
open ground_zero.algebra.group (S S.carrier Subgroup)
open ground_zero.structures (prop)
open ground_zero.types

hott theory

namespace ground_zero.algebra

  def diameter {M : Metric} (φ : S.carrier M.1) :=
  im (λ x, M.ρ x (φ.1 x))

  def limited {M : Metric} (φ : S.carrier M.1) :=
  merely (Σ m, Π x, M.ρ x (φ.1 x) ≤ m)

  @[hott] noncomputable def diameter.majorized_if_limited {M : Metric}
    (φ : S.carrier M.1) : limited φ → @majorized R.κ (diameter φ) :=
  begin
    apply merely.lift, intro H, existsi H.1, intro x, apply merely.rec, apply R.κ.prop,
    intro p, apply equiv.transport (λ y, y ≤ H.1), apply p.2, apply H.2
  end

  @[hott] noncomputable def lim (M : Metric) : (S M.1).subgroup :=
  begin
    fapply sigma.mk, existsi @limited M, intro, apply merely.uniq, split,
    { apply merely.elem, existsi R.τ.zero, intro x,
      apply equiv.transport (λ y, y ≤ R.τ.zero), symmetry,
      apply M.refl, apply @reflexive.refl R.κ }, split,
    { intros a b, apply ground_zero.HITs.merely.lift₂,
      intros p q, existsi q.1 + p.1, intro x,
      apply @transitive.trans R.κ, apply M.triangle,
      exact b.1 x, apply ineq_add, apply q.2, apply p.2 },
    { intro a, apply ground_zero.HITs.merely.lift, intro p, existsi p.1,
      intro x, apply equiv.transport (λ y, y ≤ p.1),
      symmetry, transitivity, apply M.symm, apply Id.map (M.ρ _),
      symmetry, apply equiv.forward_right a, apply p.2 }
  end

  @[hott] noncomputable def Lim (M : Metric) : pregroup :=
  Subgroup (S M.1) (lim M)

  noncomputable instance Lim.group (M : Metric) : group (Lim M) :=
  group.subgroup.group

  abbreviation Lim.carrier (M : Metric) := (Lim M).carrier
  noncomputable abbreviation Lim.φ {M : Metric} := (Lim M).φ
  noncomputable abbreviation Lim.ι {M : Metric} := (Lim M).ι

  @[hott] noncomputable def ω (M : Metric⁎) (φ : Lim.carrier M.1) : ℝ :=
  sup (diameter φ.1) (im.inh _ M.2) (diameter.majorized_if_limited φ.1 φ.2)

  @[hott] noncomputable def ω.inv_le (M : Metric⁎) (φ : Lim.carrier M.1) : ω M (Lim.ι φ) ≤ ω M φ :=
  begin
    apply sup.ssubset, intro x, apply merely.lift, intro p,
    induction p with y p, induction p, existsi (Lim.ι φ).1.1 y,
    symmetry, transitivity, apply M.1.symm,
    apply Id.map, symmetry, apply φ.1.forward_right
  end

  @[hott] noncomputable def ω.inv (M : Metric⁎) (φ : Lim.carrier M.1) : ω M (Lim.ι φ) = ω M φ :=
  begin
    apply @antisymmetric.asymm R.κ, apply ω.inv_le,
    apply equiv.transport (λ ψ, ω M ψ ≤ ω M (Lim.ι φ)),
    apply @group.inv_inv (Lim M.1), apply ω.inv_le
  end

  @[hott] noncomputable def ω.mul_rev (M : Metric⁎) (φ ψ : Lim.carrier M.1) :
    ω M (Lim.φ φ ψ) ≤ ω M ψ + ω M φ :=
  begin
    apply sup.exact, intro x, apply merely.rec, apply R.κ.prop,
    intro p, induction p with y p, induction p, apply @transitive.trans R.κ,
    apply M.1.triangle, exact ψ.1.1 y, apply ineq_add;
    { apply sup.lawful, apply im.intro }
  end

  @[hott] noncomputable def ω.mul (M : Metric⁎) (φ ψ : Lim.carrier M.1) :
    ω M (Lim.φ φ ψ) ≤ ω M φ + ω M ψ :=
  begin apply equiv.transport (λ y, ω M (Lim.φ φ ψ) ≤ y), apply R.τ⁺.mul_comm, apply ω.mul_rev end

  @[hott] noncomputable def Lim.ρ {M : Metric⁎} (g h : Lim.carrier M.1) :=
  ω M (Lim.φ g (Lim.ι h))

  @[hott] noncomputable def ω.ge_zero (M : Metric⁎) (g : Lim.carrier M.1) : 0 ≤ ω M g :=
  begin
    apply equiv.transport (λ y, y ≤ ω M g), apply sup.singleton, apply sup.sep,
    intros x y p, apply merely.rec, apply R.κ.prop, intro q,
    induction p, induction q with z q, induction q, apply M.1.positive
  end

  @[hott] noncomputable def ω.eq_zero_if_less {M : Metric⁎}
    {g : Lim.carrier M.1} : ω M g ≤ 0 → ω M g = 0 :=
  begin intro p, apply @antisymmetric.asymm R.κ, exact p, apply ω.ge_zero end

  @[hott] noncomputable def ω.unit (M : Metric⁎) : ω M (Lim M.1).e = 0 :=
  begin
    apply @antisymmetric.asymm R.κ, apply sup.exact,
    { intro y, apply merely.rec, apply R.κ.prop, intro p,
      induction p with x p, induction p, apply R.le_if_eq, apply M.1.refl },
    { apply ω.ge_zero }
  end

  @[hott] noncomputable def ω.unit_if_zero (M : Metric⁎)
    (φ : Lim.carrier M.1) (p : ω M φ = 0) : φ = (Lim M.1).e :=
  begin
    apply sigma.prod, apply ens.prop, apply ground_zero.theorems.prop.equiv_hmtpy_lem,
    intro x, apply M.1.eq_if_le_zero, apply equiv.transport (λ y, M.1.ρ (φ.1.1 x) x ≤ y),
    exact p, apply sup.lawful, apply merely.elem, existsi x, apply M.1.symm
  end

  @[hott] noncomputable def Lim.absolute (M : Metric⁎) : absolute (Lim M.1) (ω M) :=
  begin
    apply (_, (_, _)), intro x, split, apply ω.unit_if_zero,
    { intro p, transitivity, exact ω M # p, apply ω.unit },
    intro x, symmetry, apply ω.inv, apply ω.mul
  end

  @[hott] noncomputable def Lim.metrizable (M : Metric⁎) : metric (@Lim.ρ M) :=
  Absolute.metrizable (Lim M.1) ⟨ω M, Lim.absolute M⟩

  @[hott] noncomputable def Limₘ : Metric⁎ → Metric :=
  λ M, ⟨(Lim M.1).1, ⟨Lim.ρ, Lim.metrizable M⟩⟩

  @[hott] noncomputable def Lim.pointed : Metric⁎ → Metric⁎ := λ M, ⟨Limₘ M, (Lim M.1).e⟩
  notation `Lim⁎` := Lim.pointed

  @[hott] noncomputable def ω.mul_inv (M : Metric⁎) (φ ψ : Lim.carrier M.1) :
    abs (ω M φ - ω M ψ) ≤ ω M (Lim.φ φ ψ) :=
  Absolute.mul_inv (Lim M.1) ⟨ω M, Lim.absolute M⟩ φ ψ

  @[hott] noncomputable def ω.continuous (M : Metric⁎) :
    Π m, continuous⁎ (Lim⁎ M) R⁎ (ω M) m :=
  Absolute.continuous (Lim M.1) ⟨ω M, Lim.absolute M⟩
end ground_zero.algebra