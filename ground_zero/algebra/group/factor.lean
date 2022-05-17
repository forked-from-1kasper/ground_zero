import ground_zero.HITs.quotient ground_zero.algebra.group.subgroup
open ground_zero.types.equiv (biinv transport)
open ground_zero.types.Id (map)
open ground_zero.structures
open ground_zero.types
open ground_zero.proto
open ground_zero

/- Factor/quotient group (as quotient type). -/

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  open ground_zero.algebra.pregroup (right_div left_div conjugate conjugate_rev subgroup)

  variables {G : pregroup} [group G]
  local infix ` * `  := G.φ
  local notation `e` := G.e
  local postfix ⁻¹   := G.ι

  @[hott] def factor_left_rel (φ : G.subgroup) :
    G.carrier → G.carrier → Ω :=
  λ x y, ⟨ldiv φ x y, by apply ens.prop⟩

  @[hott] def factor_right_rel (φ : G.subgroup) :
    G.carrier → G.carrier → Ω :=
  λ x y, ⟨rdiv φ x y, by apply ens.prop⟩

  @[hott] def factor_eqrel_left (φ : G.subgroup) : eqrel G.carrier :=
  ⟨factor_left_rel φ, begin
    split,
    { intro x, apply transport (∈ φ),
      symmetry, apply group.mul_left_inv,
      apply φ.unit },
    split,
    { intros x y h, apply transport (∈ φ), apply inv_x_mul_y_inv,
      apply φ.inv, assumption },
    { intros x y z h g, apply transport (∈ φ),
      apply chain_ldiv x y z, apply φ.mul;
      assumption }
  end⟩

  @[hott] def factor_eqrel_right (φ : G.subgroup) : eqrel G.carrier :=
  ⟨factor_right_rel φ, begin
    split,
    { intro x, apply transport (∈ φ),
      symmetry, apply group.mul_right_inv,
      apply φ.unit },
    split,
    { intros x y h, apply transport (∈ φ),
      apply x_mul_inv_y_inv, apply φ.inv, assumption },
    { intros x y z h g, apply transport (∈ φ),
      apply chain_rdiv x y z, apply φ.mul; assumption }
  end⟩

  def factor_left (G : pregroup) (φ : G.subgroup) [group G] :=
  HITs.quotient (factor_eqrel_left φ)

  def factor_right (G : pregroup) (φ : G.subgroup) [group G] :=
  HITs.quotient (factor_eqrel_right φ)

  @[hott] noncomputable def factor_symm (φ : G.subgroup) [G ⊵ φ] :
    factor_left G φ = factor_right G φ :=
  begin
    apply map ground_zero.HITs.quotient, apply ground_zero.eqrel.eq,
    repeat { apply ground_zero.theorems.funext, intro },
    fapply ground_zero.types.sigma.prod,
    { change ldiv φ _ _ = rdiv φ _ _,
      apply HITs.interval.happly,
      apply HITs.interval.happly,
      apply cosets_eq },
    apply prop_is_prop
  end

  def factor.incl {φ : G.subgroup} [G ⊵ φ] : G.carrier → factor_left G φ :=
  ground_zero.HITs.quotient.elem

  section
    variables {φ : G.subgroup} [G ⊵ φ]

    @[hott] noncomputable def factor.mul :
      factor_left G φ → factor_left G φ → factor_left G φ :=
    begin
      fapply ground_zero.HITs.quotient.lift₂,
      { intros a b, exact factor.incl (a * b) },
      { apply ground_zero.HITs.quotient.set },
      { intros a b c d p q,
        apply ground_zero.HITs.quotient.sound,
        change _ ∈ φ, apply transport (∈ φ),
        calc b⁻¹ * (a⁻¹ * c * (d * b⁻¹)) * b
           = b⁻¹ * (a⁻¹ * c * d * b⁻¹) * b :
             (λ x, b⁻¹ * x * b) # (Id.inv $ G.mul_assoc (a⁻¹ * c) d b⁻¹)
       ... = b⁻¹ * (a⁻¹ * c * d * b⁻¹ * b) :
             G.mul_assoc b⁻¹ (a⁻¹ * c * d * b⁻¹) b
       ... = b⁻¹ * (a⁻¹ * c * d * (b⁻¹ * b)) :
             (λ x, b⁻¹ * x) # (G.mul_assoc (a⁻¹ * c * d) b⁻¹ b)
       ... = b⁻¹ * (a⁻¹ * c * d * e) :
             @map G.carrier G.carrier _ _ (λ x, b⁻¹ * (a⁻¹ * c * d * x))
               (G.mul_left_inv b)
       ... = b⁻¹ * (a⁻¹ * c * d) :
             (λ x, b⁻¹ * x) # (G.mul_one (a⁻¹ * c * d))
       ... = b⁻¹ * (a⁻¹ * (c * d)) :
             (λ x, b⁻¹ * x) # (G.mul_assoc a⁻¹ c d)
       ... = (b⁻¹ * a⁻¹) * (c * d) :
             (Id.inv $ G.mul_assoc b⁻¹ a⁻¹ (c * d))
       ... = left_div (a * b) (c * d) :
             (* (c * d)) # (Id.inv $ inv_explode a b),
        apply is_normal_subgroup.conj,
        apply φ.mul,
        { exact p },
        { apply transport (∈ φ), calc
            (b * d⁻¹)⁻¹ = d⁻¹⁻¹ * b⁻¹ : inv_explode b d⁻¹
                    ... = d * b⁻¹ : (* b⁻¹) # (inv_inv d),
          apply φ.inv,
          apply (normal_subgroup_cosets φ).left,
          exact q } }
    end

    noncomputable instance : has_mul (factor_left G φ) :=
    ⟨factor.mul⟩

    @[hott] def factor.one : factor_left G φ := factor.incl e
    instance : has_one (factor_left G φ) := ⟨factor.one⟩

    @[hott] noncomputable def factor.mul_one (x : factor_left G φ) :
      factor.mul x 1 = x :=
    begin
      fapply ground_zero.HITs.quotient.ind_prop _ _ x; clear x,
      { intro x, apply ground_zero.HITs.quotient.sound,
        apply transport (∈ φ), calc
            e = x⁻¹ * x       : Id.inv (G.mul_left_inv x)
          ... = e * x⁻¹ * x   : (* x) # (Id.inv $ G.one_mul x⁻¹)
          ... = e⁻¹ * x⁻¹ * x : (λ y, y * x⁻¹ * x) # unit_inv
          ... = (x * e)⁻¹ * x : (* x) # (Id.inv $ inv_explode x e),
        apply φ.unit },
      { intros, apply ground_zero.HITs.quotient.set }
    end

    @[hott] noncomputable def factor.one_mul (x : factor_left G φ) :
      factor.mul 1 x = x :=
    begin
      fapply ground_zero.HITs.quotient.ind_prop _ _ x; clear x,
      { intro x, change ground_zero.HITs.quotient.elem _ = _,
        apply map, apply G.one_mul },
      { intros, apply ground_zero.HITs.quotient.set }
    end

    @[hott] noncomputable def factor.assoc (x y z : factor_left G φ) :
      factor.mul (factor.mul x y) z = factor.mul x (factor.mul y z) :=
    begin
      fapply ground_zero.HITs.quotient.ind_prop _ _ x; clear x,
      { fapply ground_zero.HITs.quotient.ind_prop _ _ y; clear y,
        { fapply ground_zero.HITs.quotient.ind_prop _ _ z; clear z,
          { intros z y x, change ground_zero.HITs.quotient.elem _ = _,
            apply map, apply G.mul_assoc },
          { repeat { intros, apply ground_zero.structures.pi_prop },
            intros, apply ground_zero.HITs.quotient.set } },
        { intros, apply ground_zero.structures.pi_prop,
          intros, apply ground_zero.HITs.quotient.set } },
      { intros, apply ground_zero.HITs.quotient.set }
    end

    @[hott] noncomputable def factor.inv (x : factor_left G φ) : factor_left G φ :=
    begin
      apply ground_zero.HITs.quotient.rec _ _ _ x; clear x,
      { intro x, exact factor.incl x⁻¹ },
      { intros u v H, apply ground_zero.HITs.quotient.sound,
        apply transport (∈ φ), { symmetry, apply map (* v⁻¹), apply inv_inv },
        apply (normal_subgroup_cosets φ).left, exact H },
      { apply ground_zero.HITs.quotient.set }
    end
    noncomputable instance : has_inv (factor_left G φ) := ⟨factor.inv⟩

    @[hott] noncomputable def factor.left_inv (x : factor_left G φ) :
      factor.mul (factor.inv x) x = 1 :=
    begin
      fapply ground_zero.HITs.quotient.ind_prop _ _ x; clear x,
      { intro x, change ground_zero.HITs.quotient.elem _ = _,
        apply map, apply mul_left_inv },
      { intros, apply ground_zero.HITs.quotient.set }
    end
  end

  section
    variables (H : pregroup) (φ : H.subgroup) [group H] [H ⊵ φ]

    @[hott] noncomputable def factor : pregroup :=
    @pregroup.intro (factor_left H φ) (λ _ _, HITs.quotient.set)
      factor.mul factor.inv factor.one

    @[hott] noncomputable instance factor.semigroup : semigroup (factor H φ).magma :=
    ⟨factor.assoc⟩

    @[hott] noncomputable instance factor.monoid : monoid (factor H φ).premonoid :=
    ⟨factor.semigroup H φ, @factor.one_mul H _ φ _, factor.mul_one⟩

    @[hott] noncomputable instance factor.group : group (factor H φ) :=
    ⟨factor.monoid H φ, @factor.left_inv H _ φ _⟩
  end
  infix \ := factor

  @[hott] def factor.sound {φ : G.subgroup} [G ⊵ φ]
    {x : G.carrier} (H : x ∈ φ) : factor.incl x = 1 :> factor_left G φ :=
  begin
    apply HITs.quotient.sound, apply transport (∈ φ),
    { symmetry, apply ldiv_by_unit },
    apply φ.inv, assumption
  end

  @[hott] def factor.lift {H : pregroup} [group H] (f : G ⤳ H) {φ : G.subgroup} [G ⊵ φ]
    (p : Π x, x ∈ φ → f.fst x = H.e) : factor_left G φ → H.carrier :=
  begin
    fapply HITs.quotient.rec,
    { exact f.fst },
    { intros x y q, apply eq_of_div_eq, transitivity,
      { change H.φ _ _ = _, apply Id.map (λ x, H.φ x (f.fst y)),
        symmetry, apply homo_inv f },
      transitivity, { symmetry, apply homo_mul },
      apply p, apply q },
    { intros a b, apply Alg.hset }
  end

  @[hott] def triv.encode : G.carrier → factor_left G (triv G) := factor.incl
  @[hott] def triv.decode : factor_left G (triv G) → G.carrier :=
  begin
    fapply HITs.quotient.rec,
    exact id,
    { intros x y p, change _ = _ * _ at p,
      apply inv_inj, apply eq_inv_of_mul_eq_one,
      exact Id.inv p },
    intros a b, apply G.hset
  end

  @[hott] noncomputable def triv.factor : G ≅ G\triv G :=
  begin
    fapply mkiso, exact triv.encode,
    { intros x y, reflexivity },
    split; existsi triv.decode,
    { intro x, reflexivity },
    { fapply HITs.quotient.ind_prop; intro x,
      { reflexivity }, { apply HITs.quotient.set } }
  end

  def univ.decode : 𝟏 → factor_left G (univ G) := λ _, 1

  @[hott] noncomputable def univ_contr :
    contr (factor_left G (univ G)) :=
  begin
    existsi univ.decode ★,
    fapply HITs.quotient.ind_prop; intro x,
    { apply HITs.quotient.sound, apply ★ },
    { apply HITs.quotient.set }
  end

  @[hott] noncomputable def univ_prop :
    prop (factor_left G (univ G)) :=
  contr_impl_prop univ_contr

  @[hott] noncomputable def univ_factor : Z₁ ≅ G\univ G :=
  begin
    fapply mkiso, exact univ.decode,
    { intros x y, apply univ_prop },
    split; existsi (λ _, ★); intro x,
    apply unit_is_prop, apply univ_prop
  end

  section
    variables {φ : G.subgroup} {ψ : G.subgroup}
    variables [G ⊵ φ] [G ⊵ ψ]

    @[hott] noncomputable def factor.transfer (f : φ ⊆ ψ) :
      (G\φ).carrier → (G\ψ).carrier :=
    begin
      fapply HITs.quotient.rec,
      { exact factor.incl },
      { intros x y H, apply HITs.quotient.sound,
        apply f, exact H },
      { apply HITs.quotient.set }
    end

    @[hott] noncomputable def factor.iso
      (f : φ ⊆ ψ) (g : ψ ⊆ φ) : G\φ ≅ G\ψ :=
    begin
      fapply mkiso, exact factor.transfer f,
      { intro x, fapply HITs.quotient.ind_prop _ _ x; clear x; intro x,
        { fapply HITs.quotient.ind_prop,
          { intro y, reflexivity },
          { intros, apply HITs.quotient.set } },
        { intros, apply pi_prop,
          intro z, apply HITs.quotient.set } },
      { split; existsi factor.transfer g;
        { fapply HITs.quotient.ind_prop,
          { intro x, reflexivity },
          { intros, apply HITs.quotient.set } } }
    end
  end
end group

end ground_zero.algebra