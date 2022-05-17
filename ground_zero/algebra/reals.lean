import ground_zero.algebra.orgraph ground_zero.theorems.nat
open ground_zero.HITs (merely merely.elem merely.uniq merely.rec merely.lift)
open ground_zero.structures (zero_eqv_set hset prop pi_prop)
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

  def Metric.pointed := Σ (M : Metric), M.carrier
  notation `Metric⁎` := Metric.pointed

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

  @[hott] noncomputable def zero_le_one : (0 : ℝ) ≤ 1 :=
  begin apply equiv.transport (λ c, (0 : ℝ) ≤ c), apply R.τ⁺.one_mul, apply le_add_one end

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


  @[hott] noncomputable def R.closed (a b : ℝ) : ens ℝ :=
  ⟨λ x, a ≤ x × x ≤ b, λ x, begin apply ground_zero.structures.product_prop; apply R.κ.prop end⟩

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

  @[hott] noncomputable def double_ge_zero_impl_ge_zero {x : ℝ} : 0 ≤ x + x → 0 ≤ x :=
  begin
    intro p, cases R.total 0 x with q₁ q₂, assumption, apply ground_zero.proto.empty.elim,
    apply (strict_ineq_add R q₂ q₂).1, apply @antisymmetric.asymm R.κ,
    apply ineq_add; exact q₂.2, apply equiv.transport (λ y, y ≤ x + x),
    symmetry, apply R.τ⁺.mul_one, exact p
  end

  def tendsto {M₁ M₂ : Metric} (f : M₁.carrier → M₂.carrier) :=
  λ x₀ L, ∀ (ε : ℝ), 0 < ε → merely (Σ (δ : ℝ), (0 < δ) ×
    (Π x, 0 < M₁.ρ x x₀ → M₁.ρ x x₀ < δ → M₂.ρ (f x) L < ε))

  def continuous {M₁ M₂ : Metric} (f : M₁.carrier → M₂.carrier) :=
  λ x, tendsto f x (f x)

  def continuous.pointed (M₁ M₂ : Metric⁎) := @continuous M₁.1 M₂.1
  notation `continuous⁎` := continuous.pointed

  def absolute (G : pregroup) (φ : G.carrier → ℝ) :=
    (Π x, φ x = 0 ↔ x = G.e)
  × (Π x, φ x = φ (G.ι x))
  × (Π x y, φ (G.φ x y) ≤ φ x + φ y)

  def Absolute (G : pregroup) :=
  Σ (φ : G.carrier → ℝ), absolute G φ

  @[hott] noncomputable def Absolute.ge_zero {G : pregroup} [group G]
    (A : Absolute G) : Π x, 0 ≤ A.1 x :=
  begin
    intro x, apply double_ge_zero_impl_ge_zero, apply equiv.transport (λ w, w ≤ A.1 x + A.1 x),
    apply (A.2.1 (G.φ x (G.ι x))).right, apply group.mul_right_inv,
    apply equiv.transport (λ w, A.1 (G.φ x (G.ι x)) ≤ A.1 x + w),
    symmetry, apply (A.2.2.1 x), apply A.2.2.2
  end

  @[hott] noncomputable def Absolute.zero_if {G : pregroup} [group G]
    (A : Absolute G) : Π x, A.1 x ≤ 0 → A.1 x = 0 :=
  begin intros x p, apply @antisymmetric.asymm R.κ, exact p, apply Absolute.ge_zero end

  @[hott] def Absolute.metric (G : pregroup) [group G] (A : Absolute G) :=
  λ x y, A.1 (G.φ x (G.ι y))

  @[hott] def Absolute.metrizable (G : pregroup) [group G] (A : Absolute G) :
    metric (Absolute.metric G A) :=
  begin
    apply (_, (_, _)),
    { intros x y, split; intro p,
      { apply group.eq_of_rdiv_eq,
        apply (A.2.1 (G.φ x (G.ι y))).left, apply p },
      { apply (A.2.1 (G.φ x (G.ι y))).right,
        induction p, apply group.mul_right_inv } },
    { intros x y, transitivity, apply A.2.2.1 (G.φ x (G.ι y)),
      apply Id.map A.1, transitivity, apply group.inv_explode,
      apply Id.map (λ z, G.φ z (G.ι x)), apply group.inv_inv },
    { intros x y z, apply equiv.transport (λ w, w ≤ A.1 (G.φ x (G.ι y)) + A.1 (G.φ y (G.ι z))),
      apply Id.map A.1, apply group.chain_rdiv x y z, apply A.2.2.2 }
  end

  @[hott] def Absolute.space (G : pregroup) [group G] (A : Absolute G) : Metric :=
  ⟨G.1, ⟨Absolute.metric G A, Absolute.metrizable G A⟩⟩

  @[hott] noncomputable def Absolute.mul_inv (G : pregroup) [group G] (A : Absolute G)
    (x y : G.carrier) : abs (A.1 x - A.1 y) ≤ A.1 (G.φ x y) :=
  begin
    apply abs.le_if_minus_le_and_le,
    { apply ge_if_minus_le, apply equiv.transport (λ w, w ≤ A.1 (G.φ x y)),
      symmetry, apply @group.x_mul_inv_y_inv R.τ⁺, apply sub_le_if_add_ge_rev,
      apply equiv.transport (λ w, A.1 y ≤ w + A.1 (G.φ x y)), symmetry, apply A.2.2.1,
      apply equiv.transport (λ w, w ≤ A.1 (G.ι x) + A.1 (G.φ x y)),
      apply Id.map A.1, symmetry, apply group.rev_cancel_left x y, apply A.2.2.2 },
    { apply sub_le_if_add_ge, apply equiv.transport (λ w, A.1 x ≤ A.1 (G.φ x y) + w),
      symmetry, apply A.2.2.1, apply equiv.transport (λ w, w ≤ A.1 (G.φ x y) + A.1 (G.ι y)),
      apply Id.map A.1, symmetry, apply group.cancel_right x y, apply A.2.2.2 }
  end

  @[hott] noncomputable def triangle (x y : ℝ) : abs (x + y) ≤ abs x + abs y :=
  begin
    apply abs.le_if_minus_le_and_le,
    { apply equiv.transport (λ z, z ≤ x + y), symmetry, transitivity,
      apply @group.inv_explode R.τ⁺, apply R.τ⁺.mul_comm,
      apply ineq_add; apply abs.le },
    { apply ineq_add; apply abs.ge }
  end

  @[hott] noncomputable def R.absolute : absolute R.τ⁺ abs :=
  begin
    apply (_, (_, _)), intro x, split, apply abs.zero_if,
    { intro p, transitivity, exact abs # p, apply abs.zero },
    apply abs.even, apply triangle
  end

  @[hott] noncomputable def R.metrizable : metric (λ x y, abs (x - y)) :=
  Absolute.metrizable.{0 0} R.τ⁺ ⟨abs, R.absolute⟩

  @[hott] noncomputable def Rₘ : Metric :=
  ⟨R.1, ⟨λ x y, abs (x - y), R.metrizable⟩⟩

  @[hott] noncomputable def triangle_sub (x y z : ℝ) : abs (x - z) ≤ abs (x - y) + abs (y - z) :=
  Rₘ.triangle x y z

  @[hott] noncomputable def R.rev_triangle_ineq (x y : ℝ) : abs (abs x - abs y) ≤ abs (x + y) :=
  Absolute.mul_inv R.τ⁺ ⟨abs, R.absolute⟩ x y

  @[hott] noncomputable def R.pointed : Metric⁎ := ⟨Rₘ, R.τ⁺.e⟩
  notation `R⁎` := R.pointed

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

  @[hott] noncomputable def Absolute.continuous (G : pregroup) [group G]
    (A : Absolute G) : Π m, @continuous (Absolute.space G A) Rₘ A.1 m :=
  begin
    intros x ε H, apply merely.elem, existsi ε, split, exact H,
    intros y G₁ G₂, apply equiv.transport (λ w, abs (A.1 y - w) < ε),
    symmetry, apply A.2.2.1, apply strict_ineq_trans_left,
    apply Absolute.mul_inv, exact G₂
  end

  @[hott] noncomputable def Metric.positive (M : Metric) (x y : M.carrier) : 0 ≤ M.ρ x y :=
  begin
    apply double_ge_zero_impl_ge_zero, apply equiv.transport (λ z, z ≤ M.ρ x y + M.ρ x y),
    apply M.refl x, apply equiv.transport (λ z, M.ρ x x ≤ M.ρ x y + z),
    apply M.symm, apply M.triangle
  end

  @[hott] noncomputable def Metric.eq_if_le_zero (M : Metric) {x y : M.carrier} :
    M.ρ x y ≤ 0 → x = y :=
  begin intro p, apply M.eqv, apply @antisymmetric.asymm R.κ, exact p, apply M.positive end

  @[hott] def Closed (a b : ℝ) := (R.closed a b).subtype

  @[hott] def I := Closed 0 1
  notation `𝕀` := I

  @[hott] noncomputable def I.zero : I :=
  ⟨0, (@reflexive.refl R.κ _ _, zero_le_one)⟩

  @[hott] noncomputable def I.one : I :=
  ⟨1, (zero_le_one, @reflexive.refl R.κ _ _)⟩

  @[hott] noncomputable instance : has_zero I := ⟨I.zero⟩
  @[hott] noncomputable instance : has_one  I := ⟨I.one⟩

  @[hott] noncomputable def I.neg : 𝕀 → 𝕀 :=
  λ ⟨i, p, q⟩, begin
    existsi (1 - i), split, apply sub_ge_zero_if_le, exact q,
    apply sub_le_if_add_ge, apply equiv.transport (λ w, w ≤ 1 + i),
    apply R.τ⁺.mul_one, apply le_over_add_left, exact p
  end
end ground_zero.algebra