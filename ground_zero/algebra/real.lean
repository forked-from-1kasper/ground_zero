import ground_zero.algebra.orgraph
open ground_zero.HITs (merely merely.uniq merely.elem merely.rec merely.lift)
open ground_zero.structures (zero_eqv_set hset prop pi_prop)
open ground_zero.algebra.group (S S.carrier Subgroup)
open ground_zero.theorems
open ground_zero.types

hott theory

namespace ground_zero.algebra
  universe u

  axiom R : overring.{0 0}
  @[instance] axiom R.dedekind : dedekind R

  notation `ℝ` := Alg.carrier R

  noncomputable instance R.orfield : orfield R := R.dedekind.{0}.to_orfield
  noncomputable instance R.has_inv : has_inv ℝ := R.dedekind.{0}.to_has_inv

  def metric {α : Type u} (ρ : α → α → ℝ) :=
    (Π x y, ρ x y = 0 ↔ x = y)
  × (Π x y, ρ x y = ρ y x)
  × (Π x y z, ρ x z ≤ ρ x y + ρ y z)

  def Metric := Σ (α : 0-Type) (ρ : α.1 → α.1 → ℝ), metric ρ

  section
    variable (M : Metric)

    def Metric.carrier := M.1.1
    def Metric.hset : hset M.carrier :=
    λ _ _, zero_eqv_set.forward M.1.2

    def Metric.ρ : M.carrier → M.carrier → ℝ := M.2.1

    def Metric.refl (x : M.carrier) : M.ρ x x = 0 :=
    (M.2.2.1 x x).2 (idp x)

    def Metric.eqv (x y : M.carrier) : M.ρ x y = 0 → x = y :=
    (M.2.2.1 x y).1

    def Metric.symm (x y : M.carrier) : M.ρ x y = M.ρ y x :=
    M.2.2.2.1 x y

    def Metric.triangle (x y z : M.carrier) : M.ρ x z ≤ M.ρ x y + M.ρ y z :=
    M.2.2.2.2 x y z
  end

  def tendsto {M₁ M₂ : Metric} (f : M₁.carrier → M₂.carrier) :=
  λ x₀ L, ∀ (ε : ℝ), 0 < ε → merely (Σ (δ : ℝ), (0 < δ) ×
    (Π x, 0 < M₁.ρ x x₀ → M₁.ρ x x₀ < δ → M₂.ρ (f x) L < ε))

  def continuous {M₁ M₂ : Metric} (f : M₁.carrier → M₂.carrier) :=
  λ x, tendsto f x (f x)

  noncomputable def N.incl : ℕ → ℝ :=
  @nat.rec (λ _, ℝ) 0 (λ _ x, x + 1)

  @[hott] noncomputable def N.incl.add (n m : ℕ) : N.incl (n + m) = N.incl n + N.incl m :=
  begin
    induction m with m ih, symmetry, apply R.τ⁺.mul_one,
    transitivity, change N.incl (n + m) + 1 = _,
    apply @Id.map ℝ ℝ _ _ (+ 1) ih, apply R.τ⁺.mul_assoc
  end

  @[hott] noncomputable def le_add_one (x : ℝ) : x ≤ x + 1 :=
  begin
    apply equiv.transport (λ y, y ≤ x + 1), apply R.τ⁺.mul_one,
    apply le_over_add_left, apply one_gt_zero
  end

  @[hott] noncomputable def N.incl.lt : Π (n m : ℕ), (n ≤ m : Type) → N.incl n ≤ N.incl m
  |    0       0    := λ _, @reflexive.refl R.κ _ (N.incl 0)
  |    0    (m + 1) := λ _, @transitive.trans R.κ _ (N.incl 0) (N.incl m) (N.incl (m + 1))
    (N.incl.lt 0 m (nat.max.zero_left m)) (le_add_one (N.incl m))
  | (n + 1)    0    := λ p, ground_zero.proto.empty.elim (nat.max.ne_zero p)
  | (n + 1) (m + 1) := λ p, orfield.le_over_add (N.incl n) (N.incl m) 1 (N.incl.lt n m (nat.pred # p))

  @[hott] noncomputable def R.complete (φ : R.subset) (H : φ.inh) (G : @majorized R.κ φ) :
    Σ M, exact (@Majorant R.κ φ) M :=
  ((ground_zero.theorems.prop.prop_equiv (@supremum_uniqueness R.κ _ φ)).left
    (@complete.sup R.κ R.dedekind.to_complete φ H G))

  @[hott] noncomputable def R.cocomplete (φ : R.subset) (H : φ.inh) (G : @minorized R.κ φ) :
    Σ m, coexact (@Minorant R.κ φ) m :=
  ((ground_zero.theorems.prop.prop_equiv (@infimum_uniqueness R.κ _ φ)).left
    (@cocomplete.inf R.κ (orfield_cocomplete_if_complete R.dedekind.to_complete) φ H G))

  @[hott] noncomputable def sup (φ : R.subset) (H : φ.inh) (G : @majorized R.κ φ) : ℝ :=
  (R.complete φ H G).1

  @[hott] noncomputable def sup.lawful (φ : R.subset) (H : φ.inh) (G : @majorized R.κ φ) :
    Π x, x ∈ φ → x ≤ sup φ H G :=
  (R.complete φ H G).2.1

  @[hott] noncomputable def inf (φ : R.subset) (H : φ.inh) (G : @minorized R.κ φ) : ℝ :=
  (R.cocomplete φ H G).1

  @[hott] noncomputable def inf.lawful (φ : R.subset) (H : φ.inh) (G : @minorized R.κ φ) :
    Π x, x ∈ φ → inf φ H G ≤ x :=
  (R.cocomplete φ H G).2.1

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

  @[hott] noncomputable def ω (M : Metric) (m : M.carrier) (φ : (Lim M).carrier) : ℝ :=
  sup (diameter φ.1) (im.inh _ m) (diameter.majorized_if_limited φ.1 φ.2)
end ground_zero.algebra