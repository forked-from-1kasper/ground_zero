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

  @[hott] noncomputable def sup.exact (φ : R.subset) (H : φ.inh) (G : @majorized R.κ φ)
    (x : ℝ) (p : Π y, y ∈ φ → y ≤ x) : sup φ H G ≤ x :=
  begin apply (R.complete φ H G).2.2, apply p end

  @[hott] noncomputable def inf (φ : R.subset) (H : φ.inh) (G : @minorized R.κ φ) : ℝ :=
  (R.cocomplete φ H G).1

  @[hott] noncomputable def inf.lawful (φ : R.subset) (H : φ.inh) (G : @minorized R.κ φ) :
    Π x, x ∈ φ → inf φ H G ≤ x :=
  (R.cocomplete φ H G).2.1

  @[hott] noncomputable def inf.exact (φ : R.subset) (H : φ.inh) (G : @minorized R.κ φ)
    (x : ℝ) (p : Π y, y ∈ φ → x ≤ y) : x ≤ inf φ H G :=
  begin apply (R.cocomplete φ H G).2.2, apply p end

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

  def Metric.pointed := Σ (M : Metric), M.carrier
  notation `Metric⁎` := Metric.pointed

  @[hott] noncomputable def ω (M : Metric⁎) (φ : Lim.carrier M.1) : ℝ :=
  sup (diameter φ.1) (im.inh _ M.2) (diameter.majorized_if_limited φ.1 φ.2)

  @[hott] noncomputable def sup.eqv {φ ψ : R.subset} {H₁ : φ.inh} {H₂ : ψ.inh}
    {G₁ : @majorized R.κ φ} {G₂ : @majorized R.κ ψ} (p : φ = ψ) : sup φ H₁ G₁ = sup ψ H₂ G₂ :=
  begin induction p, apply equiv.bimap; apply merely.uniq end

  @[hott] noncomputable def sup.le {φ ψ : R.subset} {H₁ : φ.inh} {H₂ : ψ.inh}
    {G₁ : @majorized R.κ φ} {G₂ : @majorized R.κ ψ} (y : ℝ) (p : y ∈ ψ)
    (r : Π x, x ∈ φ → x ≤ y) : sup φ H₁ G₁ ≤ sup ψ H₂ G₂ :=
  begin
    apply sup.exact, intros x q, apply @transitive.trans R.κ _,
    apply r, exact q, apply sup.lawful, exact p
  end

  @[hott] noncomputable def sup.sep {φ ψ : R.subset} {H₁ : φ.inh} {H₂ : ψ.inh}
    {G₁ : @majorized R.κ φ} {G₂ : @majorized R.κ ψ} (r : Π x y, x ∈ φ → y ∈ ψ → x ≤ y) :
      sup φ H₁ G₁ ≤ sup ψ H₂ G₂ :=
  begin
    apply merely.rec _ _ H₂, apply R.κ.prop, intro p, induction p with y p,
    apply sup.le, apply p, intros x q, apply r; assumption
  end

  @[hott] noncomputable def sup.ssubset {φ ψ : R.subset} {H₁ : φ.inh} {H₂ : ψ.inh}
    {G₁ : @majorized R.κ φ} {G₂ : @majorized R.κ ψ} (r : φ ⊆ ψ) : sup φ H₁ G₁ ≤ sup ψ H₂ G₂ :=
  begin apply sup.exact, intros y p, apply sup.lawful, apply r, assumption end

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

  @[hott] noncomputable def R.not_not_total (x y : ℝ) : (x ≤ y) → (x > y) → 𝟎 :=
  begin intros p q, apply q.1, apply @antisymmetric.asymm R.κ, exact q.2, exact p end

  @[hott] noncomputable def R.total_is_prop (x y : ℝ) : prop ((x ≤ y) + (x > y)) :=
  begin
    intros p q, induction p with p₁ p₂; induction q with q₁ q₂,
    { apply Id.map, apply R.κ.prop },
    { apply ground_zero.proto.empty.elim, apply R.not_not_total x y; assumption },
    { apply ground_zero.proto.empty.elim, apply R.not_not_total x y; assumption },
    { apply Id.map, induction p₂ with p p', induction q₂ with q q',
      apply product.prod, apply ground_zero.structures.not_is_prop, apply R.κ.prop }
  end

  @[hott] noncomputable def R.total (x y : ℝ) : (x ≤ y) + (x > y) :=
  begin
    apply (ground_zero.theorems.prop.prop_equiv _).left,
    apply merely.lift _ (@connected.total R.κ _ x y),
    { intro H, induction H with p q, left, assumption,
      cases @classical.lem (x = y) _ with p₁ p₂,
      left, induction p₁, apply @reflexive.refl R.κ,
      right, split, intro r, apply p₂,
      exact Id.symm r, exact q, apply R.hset },
    { apply R.total_is_prop }
  end

  @[hott] noncomputable def abs (x : ℝ) : ℝ :=
  coproduct.elim (λ _, x) (λ _, -x) (R.total 0 x)

  @[hott] noncomputable def abs.pos {x : ℝ} (p : 0 ≤ x) : abs x = x :=
  begin
    change coproduct.elim _ _ _ = _, cases R.total 0 x with q₁ q₂,
    reflexivity, apply ground_zero.proto.empty.elim,
    apply R.not_not_total 0 x; assumption
  end

  @[hott] noncomputable def R.zero_eq_minus_zero {x : ℝ} (p : x = 0) : x = -x :=
  begin
    transitivity, exact p, symmetry,
    transitivity, apply Id.map, exact p,
    symmetry, apply @group.unit_inv R.τ⁺
  end

  @[hott] noncomputable def abs.neg {x : ℝ} (p : x ≤ 0) : abs x = -x :=
  begin
    change coproduct.elim _ _ _ = _, cases R.total 0 x with q₁ q₂,
    change x = -x, apply R.zero_eq_minus_zero,
    apply @antisymmetric.asymm R.κ; assumption, reflexivity
  end

  @[hott] noncomputable def R.zero_le_impl_zero_ge_minus {x : ℝ} (p : 0 ≤ x) : -x ≤ 0 :=
  begin
    apply equiv.transport (λ y, -x ≤ y), symmetry,
    apply @group.unit_inv R.τ⁺, apply minus_inv_sign, exact p
  end

  @[hott] noncomputable def R.zero_le_minus_impl_zero_ge {x : ℝ} (p : 0 ≤ -x) : x ≤ 0 :=
  begin
    apply equiv.transport (λ (y : ℝ), y ≤ 0), apply @group.inv_inv R.τ⁺,
    apply R.zero_le_impl_zero_ge_minus, assumption
  end

  @[hott] noncomputable def R.zero_ge_minus_impl_zero_le {x : ℝ} (p : -x ≤ 0) : 0 ≤ x :=
  begin
    apply inv_minus_sign, apply equiv.transport (λ y, -x ≤ y),
    apply @group.unit_inv R.τ⁺, exact p
  end

  @[hott] noncomputable def R.zero_ge_impl_zero_le_minus {x : ℝ} (p : x ≤ 0) : 0 ≤ -x :=
  begin
    apply R.zero_ge_minus_impl_zero_le, apply equiv.transport (λ (y : ℝ), y ≤ 0),
    symmetry, apply @group.inv_inv R.τ⁺, assumption
  end

  @[hott] noncomputable def abs.even (x : ℝ) : abs x = abs (-x) :=
  begin
    cases (R.total 0 x) with p q,
    { transitivity, apply abs.pos p, symmetry,
      transitivity, apply abs.neg,
      apply R.zero_le_impl_zero_ge_minus p,
      apply @group.inv_inv R.τ⁺ },
    { transitivity, apply abs.neg q.2, symmetry, apply abs.pos,
      apply R.zero_ge_impl_zero_le_minus q.2 }
  end

  @[hott] noncomputable def abs.ge (x : ℝ) : x ≤ abs x :=
  begin
    cases (R.total 0 x) with p q,
    { apply equiv.transport (λ y, x ≤ y), symmetry,
      apply abs.pos p, apply @reflexive.refl R.κ },
    { apply equiv.transport (λ y, x ≤ y), symmetry,
      apply abs.neg q.2, apply @transitive.trans R.κ,
      apply q.2, apply R.zero_ge_impl_zero_le_minus q.2 }
  end

  @[hott] noncomputable def abs.le (x : ℝ) : -(abs x) ≤ x :=
  begin
    cases (R.total 0 x) with p q,
    { apply equiv.transport (λ (y : ℝ), y ≤ x), symmetry,
      apply Id.map, apply abs.pos p, apply @transitive.trans R.κ,
      apply R.zero_le_impl_zero_ge_minus p, assumption },
    { apply equiv.transport (λ (y : ℝ), y ≤ x), symmetry,
      transitivity, apply Id.map, apply abs.neg q.2,
      apply @group.inv_inv R.τ⁺, apply @reflexive.refl R.κ }
  end

  @[hott] noncomputable def abs.le_if_minus_le_and_le (x y : ℝ) (r₁ : -x ≤ y) (r₂ : y ≤ x) : abs y ≤ x :=
  begin
    cases (R.total 0 y) with p q,
    { apply equiv.transport (λ z, z ≤ x), symmetry,
      apply abs.pos p, assumption },
    { apply equiv.transport (λ z, z ≤ x), symmetry,
      apply abs.neg q.2, apply inv_minus_sign,
      apply equiv.transport (λ z, -x ≤ z), symmetry,
      apply @group.inv_inv R.τ⁺, assumption }
  end

  @[hott] noncomputable def abs.ge_zero (x : ℝ) : 0 ≤ abs x :=
  begin
    cases (R.total 0 x) with p q,
    { apply equiv.transport (λ (y : ℝ), 0 ≤ y),
      symmetry, apply abs.pos p, assumption },
    { apply equiv.transport (λ (y : ℝ), 0 ≤ y), symmetry, apply abs.neg q.2,
      apply R.zero_ge_impl_zero_le_minus, exact q.2, }
  end

  @[hott] noncomputable def abs.le_if_abs_le (x y : ℝ) (r : abs y ≤ x) : y ≤ x :=
  begin apply @transitive.trans R.κ, apply abs.ge, assumption end

  @[hott] noncomputable def abs.ge_if_abs_le (x y : ℝ) (r : abs y ≤ x) : -x ≤ y :=
  begin
    apply ge_if_minus_le, apply @transitive.trans R.κ,
    apply ge_if_minus_le, apply abs.le, assumption
  end

  @[hott] noncomputable def triangle (x y : ℝ) : abs (x + y) ≤ abs x + abs y :=
  begin
    apply abs.le_if_minus_le_and_le,
    { apply equiv.transport (λ z, z ≤ x + y), symmetry, transitivity,
      apply @group.inv_explode R.τ⁺, apply R.τ⁺.mul_comm,
      apply ineq_add; apply abs.le },
    { apply ineq_add; apply abs.ge }
  end

  @[hott] noncomputable def triangle_sub (x y z : ℝ) : abs (x - z) ≤ abs (x - y) + abs (y - z) :=
  begin
    apply equiv.transport (λ w, w ≤ abs (x - y) + abs (y - z)),
    apply Id.map abs, apply @group.chain_rdiv R.τ⁺ _ x y z, apply triangle
  end

  @[hott] noncomputable def abs.zero : abs 0 = 0 :=
  begin apply abs.pos, apply @reflexive.refl R.κ end

  @[hott] noncomputable def R.le_if_eq {x y : ℝ} (p : x = y) : x ≤ y :=
  begin induction p, apply @reflexive.refl R.κ end

  @[hott] noncomputable def R.ge_if_eq {x y : ℝ} (p : x = y) : x ≤ y :=
  begin induction p, apply @reflexive.refl R.κ end

  @[hott] noncomputable def abs.zero_if (x : ℝ) (p : abs x = 0) : x = 0 :=
  begin
    apply @antisymmetric.asymm R.κ, { induction p, apply abs.ge },
    { apply equiv.transport (λ y, y ≤ x), symmetry, apply @group.unit_inv R.τ⁺,
      apply @transitive.trans R.κ, apply minus_inv_sign,
      apply R.le_if_eq p, apply abs.le }
  end

  @[hott] noncomputable def R.metrizable : metric (λ x y, abs (x - y)) :=
  begin
    apply (_, (_, _)),
    { intros x y, split; intro p,
      { apply @group.eq_of_rdiv_eq R.τ⁺,
        apply abs.zero_if, assumption },
      { induction p, change abs (x - x) = _, transitivity,
        apply Id.map, apply @group.mul_right_inv R.τ⁺, apply abs.zero } },
    { intros x y, transitivity, apply abs.even, apply Id.map,
      transitivity, apply @group.inv_explode R.τ⁺,
      apply Id.map (λ z, z - x), apply @group.inv_inv R.τ⁺ },
    { apply triangle_sub }
  end

  @[hott] noncomputable def Rₘ : Metric :=
  ⟨R.1, ⟨λ x y, abs (x - y), R.metrizable⟩⟩

  @[hott] noncomputable def R.pointed : Metric⁎ := ⟨Rₘ, R.τ⁺.e⟩
  notation `R⁎` := R.pointed

  @[hott] noncomputable def Lim.ρ {M : Metric⁎} (g h : Lim.carrier M.1) :=
  ω M (Lim.φ g (Lim.ι h))

  @[hott] noncomputable def R.singleton : ℝ → ens ℝ :=
  ens.singleton (λ _ _, R.hset)

  @[hott] noncomputable def R.singl_inh : Π x, (R.singleton x).inh :=
  ens.singleton_inh (λ _ _, R.hset)

  @[hott] noncomputable def R.singl_majorized (x : ℝ) : @majorized R.κ (R.singleton x) :=
  begin apply merely.elem, existsi x, intros y p, induction p, apply @reflexive.refl R.κ end

  @[hott] noncomputable def sup.singleton (x : ℝ) :
    sup (R.singleton x) (R.singl_inh x) (R.singl_majorized x) = x :=
  begin
    apply @antisymmetric.asymm R.κ,
    { apply sup.exact, intros y p, induction p, apply @reflexive.refl R.κ },
    { apply sup.lawful, change _ = _, reflexivity }
  end

  @[hott] noncomputable def double_ge_zero_impl_ge_zero {x : ℝ} : 0 ≤ x + x → 0 ≤ x :=
  begin
    intro p, cases R.total 0 x with q₁ q₂, assumption, apply ground_zero.proto.empty.elim,
    apply (strict_ineq_add R q₂ q₂).1, apply @antisymmetric.asymm R.κ,
    apply ineq_add; exact q₂.2, apply equiv.transport (λ y, y ≤ x + x),
    symmetry, apply R.τ⁺.mul_one, exact p
  end

  @[hott] noncomputable def Metric.positive (M : Metric) (x y : M.carrier) : 0 ≤ M.ρ x y :=
  begin
    apply double_ge_zero_impl_ge_zero, apply equiv.transport (λ z, z ≤ M.ρ x y + M.ρ x y),
    apply M.refl x, apply equiv.transport (λ z, M.ρ x x ≤ M.ρ x y + z),
    apply M.symm, apply M.triangle
  end

  @[hott] noncomputable def ω.ge_zero (M : Metric⁎) (g : Lim.carrier M.1) : 0 ≤ ω M g :=
  begin
    apply equiv.transport (λ y, y ≤ ω M g), apply sup.singleton, apply sup.sep,
    intros x y p, apply merely.rec, apply R.κ.prop, intro q,
    induction p, induction q with z q, induction q, apply M.1.positive
  end

  @[hott] noncomputable def Metric.eq_if_le_zero (M : Metric) {x y : M.carrier} :
    M.ρ x y ≤ 0 → x = y :=
  begin intro p, apply M.eqv, apply @antisymmetric.asymm R.κ, exact p, apply M.positive end

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

  @[hott] noncomputable def Lim.metrizable (M : Metric⁎) : metric (@Lim.ρ M) :=
  begin
    apply (_, (_, _)),
    { intros x y, split; intro p,
      { apply group.eq_of_rdiv_eq, apply ω.unit_if_zero,
        change ω _ _ = _ at p, exact p },
      { induction p, transitivity, apply Id.map (ω M),
        apply group.mul_right_inv, apply ω.unit } },
    { intros x y, transitivity, symmetry, apply ω.inv,
      apply Id.map (ω M), transitivity, apply group.inv_explode,
      apply Id.map (λ z, Lim.φ z (Lim.ι x)), apply group.inv_inv },
    { intros x y z, apply equiv.transport (λ w, w ≤ Lim.ρ x y + Lim.ρ y z),
      apply Id.map (ω M), apply group.chain_rdiv x y z, apply ω.mul }
  end

  @[hott] noncomputable def Limₘ : Metric⁎ → Metric :=
  λ M, ⟨(Lim M.1).1, ⟨Lim.ρ, Lim.metrizable M⟩⟩

  @[hott] noncomputable def Lim.pointed : Metric⁎ → Metric⁎ := λ M, ⟨Limₘ M, (Lim M.1).e⟩
  notation `Lim⁎` := Lim.pointed

  @[hott] noncomputable def ω.mul_inv (M : Metric⁎) (φ ψ : Lim.carrier M.1) :
    abs (ω M φ - ω M ψ) ≤ ω M (Lim.φ φ ψ) :=
  begin
    apply abs.le_if_minus_le_and_le,
    { apply ge_if_minus_le, apply equiv.transport (λ y, y ≤ ω M (Lim.φ φ ψ)),
      symmetry, apply @group.x_mul_inv_y_inv R.τ⁺, apply sub_le_if_add_ge_rev,
      apply equiv.transport (λ w, ω M ψ ≤ w + ω M (Lim.φ φ ψ)), apply ω.inv,
      apply equiv.transport (λ w, w ≤ ω M (Lim.ι φ) + ω M (Lim.φ φ ψ)),
      apply Id.map (ω M), symmetry, apply group.rev_cancel_left φ ψ, apply ω.mul },
    { apply sub_le_if_add_ge, apply equiv.transport (λ w, ω M φ ≤ ω M (Lim.φ φ ψ) + w),
      apply ω.inv, apply equiv.transport (λ w, w ≤ ω M (Lim.φ φ ψ) + ω M (Lim.ι ψ)),
      apply Id.map (ω M), symmetry, apply group.cancel_right φ ψ, apply ω.mul }
  end

  def tendsto {M₁ M₂ : Metric} (f : M₁.carrier → M₂.carrier) :=
  λ x₀ L, ∀ (ε : ℝ), 0 < ε → merely (Σ (δ : ℝ), (0 < δ) ×
    (Π x, 0 < M₁.ρ x x₀ → M₁.ρ x x₀ < δ → M₂.ρ (f x) L < ε))

  def continuous {M₁ M₂ : Metric} (f : M₁.carrier → M₂.carrier) :=
  λ x, tendsto f x (f x)

  def continuous.pointed (M₁ M₂ : Metric⁎) := @continuous M₁.1 M₂.1
  notation `continuous⁎` := continuous.pointed

  @[hott] noncomputable def ω.continuous (M : Metric⁎) :
    Π m, continuous⁎ (Lim⁎ M) R⁎ (ω M) m :=
  begin
    intros x ε H, apply merely.elem, existsi ε, split, exact H,
    intros y G₁ G₂, apply equiv.transport (λ w, abs (ω M y - w) < ε),
    apply ω.inv, apply strict_ineq_trans_left, apply ω.mul_inv, exact G₂
  end
end ground_zero.algebra