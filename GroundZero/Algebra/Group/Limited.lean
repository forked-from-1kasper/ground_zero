import GroundZero.Algebra.Group.Symmetric
import GroundZero.Algebra.Reals

open GroundZero.Structures
open GroundZero.Types
open GroundZero.HITs

namespace GroundZero.Algebra
  def diameter {M : Metric} (φ : Group.S.carrier M.1) :=
  im (λ x, M.ρ x (φ.1 x))

  def limited {M : Metric} (φ : Group.S.carrier M.1) :=
  ∥Σ m, Π x, R.ρ (M.ρ x (φ.1 x)) m∥

  noncomputable hott def diameter.majorizedIfLimited {M : Metric}
    (φ : Group.S.carrier M.1) : limited φ → @majorized R.κ (diameter φ) :=
  begin
    apply Merely.lift; intro H; existsi H.1; intro x; apply Merely.rec; apply R.κ.prop;
    intro p; apply Equiv.transport (R.ρ · _); apply p.2; apply H.2
  end

  noncomputable hott def lim (M : Metric) : (Group.S M.1).subgroup :=
  begin
    fapply Sigma.mk; existsi @limited M; intro; apply Merely.uniq; apply Prod.mk;
    { apply Merely.elem; existsi R.τ.zero; intro x;
      apply Equiv.transport (R.ρ · _); symmetry;
      apply M.refl; apply @reflexive.refl R.κ }; apply Prod.mk;
    { intros a b; apply Merely.lift₂;
      intros p q; existsi q.1 + p.1; intro x;
      apply @transitive.trans R.κ; apply M.triangle;
      exact b.1 x; apply ineqAdd; apply q.2; apply p.2 };
    { intro a; apply Merely.lift; intro p; existsi p.1;
      intro x; apply Equiv.transport (R.ρ · _);
      symmetry; transitivity; apply M.symm; apply Id.map (M.ρ _);
      symmetry; apply Equiv.forwardRight a; apply p.2 }
  end

  noncomputable hott def Lim (M : Metric) : Group :=
  Group.Subgroup (Group.S M.1) (lim M)

  abbrev Lim.carrier (M : Metric) := (Lim M).carrier
  noncomputable abbrev Lim.φ {M : Metric} := (Lim M).φ
  noncomputable abbrev Lim.ι {M : Metric} := (Lim M).ι

  noncomputable hott def ω (M : Metric⁎) (φ : Lim.carrier M.1) : ℝ :=
  sup (diameter φ.1) (im.inh _ M.2) (diameter.majorizedIfLimited φ.1 φ.2)

  noncomputable hott def ω.invLe (M : Metric⁎) (φ : Lim.carrier M.1) : R.ρ (ω M (Lim.ι φ)) (ω M φ) :=
  begin
    apply sup.ssubset; intro x; apply Merely.lift; intro ⟨y, p⟩;
    existsi (Lim.ι φ).1.1 y; transitivity; apply M.1.symm;
    transitivity; apply Id.map (M.1.ρ · _);
    apply φ.1.forwardRight; exact p
  end

  noncomputable hott def ω.inv (M : Metric⁎) (φ : Lim.carrier M.1) : ω M (Lim.ι φ) = ω M φ :=
  begin
    apply @antisymmetric.asymm R.κ; apply ω.invLe;
    apply Equiv.transport (λ ψ, R.ρ (ω M ψ) (ω M (Lim.ι φ)));
    apply @Group.invInv (Lim M.1); apply ω.invLe
  end

  noncomputable hott def ω.mulRev (M : Metric⁎) (φ ψ : Lim.carrier M.1) :
    R.ρ (ω M (Lim.φ φ ψ)) (ω M ψ + ω M φ) :=
  begin
    apply sup.exact; intro x; apply Merely.rec; apply R.κ.prop;
    intro ⟨y, p⟩; induction p; apply @transitive.trans R.κ;
    apply M.1.triangle; exact ψ.1.1 y; apply ineqAdd <;>
    { apply sup.lawful; apply im.intro }
  end

  noncomputable hott def ω.mul (M : Metric⁎) (φ ψ : Lim.carrier M.1) :
    R.ρ (ω M (Lim.φ φ ψ)) (ω M φ + ω M ψ) :=
  begin apply Equiv.transport (R.ρ (ω M (Lim.φ φ ψ))); apply R.τ.addComm; apply ω.mulRev end

  noncomputable hott def Lim.ρ {M : Metric⁎} (g h : Lim.carrier M.1) :=
  ω M (Lim.φ g (Lim.ι h))

  noncomputable hott def ω.geZero (M : Metric⁎) (g : Lim.carrier M.1) : R.ρ 0 (ω M g) :=
  begin
    apply Equiv.transport (R.ρ · _); apply sup.singleton; apply sup.sep;
    intros x y p; apply Merely.rec; apply R.κ.prop; intro ⟨z, q⟩;
    induction p; induction q; apply M.1.positive
  end

  noncomputable hott def ω.eqZeroIfLess {M : Metric⁎}
    {g : Lim.carrier M.1} : R.ρ (ω M g) 0 → ω M g = 0 :=
  begin intro p; apply @antisymmetric.asymm R.κ; exact p; apply ω.geZero end

  noncomputable hott def ω.unit (M : Metric⁎) : ω M (Lim M.1).e = 0 :=
  begin
    apply @antisymmetric.asymm R.κ; apply sup.exact;
    { intro y; apply Merely.rec; apply R.κ.prop; intro ⟨x, p⟩;
      induction p; apply R.leIfEq; apply M.1.refl };
    { apply ω.geZero }
  end

  noncomputable hott def ω.unitIfZero (M : Metric⁎)
    (φ : Lim.carrier M.1) (p : ω M φ = 0) : φ = (Lim M.1).e :=
  begin
    apply Sigma.prod; apply Ens.prop; apply GroundZero.Theorems.Equiv.equivHmtpyLem;
    intro x; apply M.1.eqIfLeZero; apply Equiv.transport (R.ρ (M.1.ρ (φ.1.1 x) x));
    exact p; apply sup.lawful; apply Merely.elem; existsi x; apply M.1.symm
  end

  noncomputable hott def Lim.absolute (M : Metric⁎) : absolute (Lim M.1) (ω M) :=
  begin
    apply (_, (_, _)); intro x; apply Prod.mk; apply ω.unitIfZero;
    { intro p; transitivity; exact Id.map (ω M) p; apply ω.unit };
    intro x; symmetry; apply ω.inv; apply ω.mul
  end

  noncomputable hott def Lim.metrizable (M : Metric⁎) : metric (@Lim.ρ M) :=
  Absolute.metrizable (Lim M.1) ⟨ω M, Lim.absolute M⟩

  noncomputable hott def Limₘ : Metric⁎ → Metric :=
  λ M, ⟨(Lim M.1).1.1, ⟨Lim.ρ, Lim.metrizable M⟩⟩

  -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

  --noncomputable hott def Lim.pointed : Metric⁎ → Metric⁎ := λ M, ⟨Limₘ M, (Lim M.1).e⟩
  --notation "Lim⁎" => Lim.pointed

  --noncomputable hott def ω.mulInv (M : Metric⁎) (φ ψ : Lim.carrier M.1) :
  --  R.ρ (abs (ω M φ - ω M ψ)) (ω M (Lim.φ φ ψ)) :=
  --Absolute.mulInv (Lim M.1) ⟨ω M, Lim.absolute M⟩ φ ψ

  --noncomputable hott def ω.continuous (M : Metric⁎) :
  --  Π m, continuous⁎ (Lim⁎ M) R⁎ (ω M) m :=
  --Absolute.continuous (Lim M.1) ⟨ω M, Lim.absolute M⟩
end GroundZero.Algebra
