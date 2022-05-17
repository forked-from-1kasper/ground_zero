import ground_zero.algebra.group.basic
open ground_zero.types.equiv (biinv transport)
open ground_zero.types.Id (map)
open ground_zero.structures
open ground_zero.types
open ground_zero.proto
open ground_zero

/-
  Kernel and image of homomorphism.
  Subgroup, normal subgroup.
-/

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  open ground_zero.algebra.pregroup (right_div left_div conjugate conjugate_rev subgroup)

  variables {G : pregroup} [group G]
  local infix ` * `  := G.φ
  local notation `e` := G.e
  local postfix ⁻¹   := G.ι

  local infix ^ := @conjugate G
  local infix / := @right_div G

  def normal (G : pregroup) (φ : G.subset) :=
  Π g h, G.φ g h ∈ φ → G.φ h g ∈ φ

  class is_normal_subgroup (G : pregroup) (φ : G.subgroup) :=
  (cosets_eqv : normal G φ.set)

  notation φ ` ⊴ `:50 G := is_normal_subgroup G φ
  infix ` ⊵ `:50 := is_normal_subgroup

  @[hott] def is_subgroup.prop (φ : G.subset) : prop (pregroup.is_subgroup G φ) :=
  begin
    apply product_prop, apply ens.prop,
    apply product_prop; repeat { apply pi_prop, intro };
    apply ens.prop
  end

  @[hott] def subgroup.ext {φ ψ : G.subgroup} : φ.set = ψ.set → φ = ψ :=
  begin
    induction φ with φ p, induction ψ with ψ q,
    intro r, change φ = ψ at r, induction r,
    apply Id.map, apply is_subgroup.prop
  end

  @[hott] def is_normal_subgroup.conj (φ : G.subgroup)
    [G ⊵ φ] (n g : G.carrier) : n ∈ φ → n ^ g ∈ φ :=
  begin
    intro h, change g⁻¹ * n * g ∈ φ,
    apply ground_zero.types.equiv.transport (∈ φ),
    { symmetry, apply G.mul_assoc },
    apply is_normal_subgroup.cosets_eqv,
    apply ground_zero.types.equiv.transport (∈ φ),
    apply cancel_right, assumption
  end

  @[hott] def conjugate_eqv (φ : G.subgroup) [G ⊵ φ] (n g : G.carrier) :
    @conjugate G n g ∈ φ → @conjugate_rev G n g ∈ φ :=
  begin
    intro h, apply is_normal_subgroup.cosets_eqv,
    apply transport (∈ φ),
    calc g * (g⁻¹ * n) = (g * g⁻¹) * n : Id.inv (G.mul_assoc g g⁻¹ n)
                   ... = e * n         : (* n) # (mul_right_inv g)
                   ... = (g⁻¹ * g) * n : (* n) # (Id.inv $ G.mul_left_inv g)
                   ... = g⁻¹ * (g * n) : G.mul_assoc g⁻¹ g n,
    apply is_normal_subgroup.cosets_eqv, assumption
  end

  @[hott] def normal_subgroup_cosets (φ : G.subgroup) [G ⊵ φ] :
    Π {x y : G.carrier}, ldiv φ x y ↔ rdiv φ x y :=
  begin
    intros x y, split; intro h,
    { change x * y⁻¹ ∈ φ, apply transport (∈ φ),
      calc x * (y⁻¹ * x) * x⁻¹ = x * (y⁻¹ * x * x⁻¹) :
                                 G.mul_assoc x (left_div y x) x⁻¹
                           ... = x * y⁻¹ : (G.φ x) # (Id.inv $ cancel_right y⁻¹ x),
      apply conjugate_eqv,
      apply is_normal_subgroup.conj,
      apply transport (∈ φ), apply inv_x_mul_y_inv,
      apply φ.inv, assumption },
    { change x⁻¹ * y ∈ φ, apply transport (∈ φ),
      calc x⁻¹ * (y * x⁻¹) * x = x⁻¹ * (y * x⁻¹ * x) :
                                 G.mul_assoc x⁻¹ (y / x) x
                           ... = x⁻¹ * y : (G.φ x⁻¹) # (Id.inv $ cancel_left y x),
      apply is_normal_subgroup.conj, apply transport (∈ φ),
      apply x_mul_inv_y_inv,
      apply φ.inv, assumption }
  end

  @[hott] noncomputable def cosets_eq (φ : G.subgroup) [G ⊵ φ] : ldiv φ = rdiv φ :=
  begin
    repeat { apply ground_zero.theorems.funext, intro },
    apply ground_zero.ua.propext,
    repeat { apply ens.prop },
    apply normal_subgroup_cosets
  end

  section
    variables {H : pregroup} {φ : H.subgroup}
    include H

    @[hott] def subgroup.mul (x y : φ.subtype) : φ.subtype :=
    begin existsi H.φ x.1 y.1, apply φ.mul, apply x.2, apply y.2 end
    local infix ` ∗ `:70 := @subgroup.mul H φ

    @[hott] def subgroup.inv (x : φ.subtype) : φ.subtype :=
    begin existsi H.ι x.1, apply φ.inv, apply x.2 end

    @[hott] def subgroup.unit : φ.subtype := ⟨H.e, φ.unit⟩

    @[hott] def subgroup.ens : hset φ.subtype :=
    begin apply ens.hset, intros a b, apply Alg.hset end

    @[hott] def subgroup.mul_assoc [group H] (x y z : φ.subtype) : x ∗ y ∗ z = x ∗ (y ∗ z) :=
    begin
      induction x with x A, induction y with y B, induction z with z C,
      fapply ground_zero.types.sigma.prod,
      apply H.mul_assoc, apply ens.prop
    end

    @[hott] def subgroup.one_mul [group H] (x : φ.subtype) : subgroup.unit ∗ x = x :=
    begin
      induction x with x p,
      fapply ground_zero.types.sigma.prod,
      apply H.one_mul, apply ens.prop
    end

    @[hott] def subgroup.mul_one [group H] (x : φ.subtype) : x ∗ subgroup.unit = x :=
    begin
      induction x with x p,
      fapply ground_zero.types.sigma.prod,
      apply H.mul_one, apply ens.prop
    end

    @[hott] def subgroup.mul_left_inv [group H] (x : φ.subtype) :
      subgroup.inv x ∗ x = subgroup.unit :=
    begin
      induction x with x p,
      fapply ground_zero.types.sigma.prod,
      apply group.mul_left_inv, apply ens.prop
    end

    @[hott] def Subgroup (H : pregroup) (φ : H.subgroup) : pregroup :=
    @pregroup.intro φ.subtype (λ _ _, subgroup.ens)
      subgroup.mul subgroup.inv subgroup.unit

    @[hott] instance subgroup.semigroup [group H] : semigroup (Subgroup H φ).magma :=
    ⟨subgroup.mul_assoc⟩

    @[hott] instance subgroup.monoid [group H] : monoid (Subgroup H φ).premonoid :=
    ⟨subgroup.semigroup, subgroup.one_mul, subgroup.mul_one⟩

    @[hott] instance subgroup.group [group H] : group (Subgroup H φ) :=
    ⟨subgroup.monoid, subgroup.mul_left_inv⟩
  end

  @[hott] def Subgroup.ext (φ ψ : G.subgroup) :
    φ.set = ψ.set → Subgroup G φ = Subgroup G ψ :=
  begin
    cases φ with φ p, cases ψ with ψ q, intro r,
    apply Id.map (Subgroup G), apply subgroup.ext r
  end

  @[hott] def inter (φ ψ : G.subgroup) : subgroup (Subgroup G ψ) :=
  begin
    fapply pregroup.subgroup.mk,
    exact ⟨λ x, x.fst ∈ φ, λ x, ens.prop x.fst φ.set⟩,
    { change e ∈ φ, apply φ.unit },
    { intros a b G H, induction a with a g,
      induction b with b h, change _ ∈ φ,
      apply φ.mul; assumption },
    { intros a G, induction a with a g,
      change _ ∈ φ, apply φ.inv,
      assumption }
  end

  @[hott] instance abelian_subgroup_is_normal (G : pregroup) [abelian G]
    (φ : G.subgroup) : G ⊵ φ :=
  begin
    split, intros g h p, apply transport (∈ φ),
    apply pregroup.mul_comm, assumption
  end

  @[hott] instance abelian_subgroup_is_abelian (G : pregroup) [abelian G]
    (φ : G.subgroup) : abelian (Subgroup G φ) :=
  begin
    split, intros a b, induction a with a p, induction b with b q,
    fapply sigma.prod, apply pregroup.mul_comm G, apply ens.prop
  end

  @[hott] def homo.surj (φ : G.subgroup) : Subgroup G φ ⤳ G :=
  mkhomo sigma.fst (λ ⟨a, _⟩ ⟨b, _⟩, idp (a * b))

  section
    variables {H : pregroup} [group H] (φ : G ⤳ H)
    local infix × : 70 := H.φ

    def ker.aux := λ g, φ.fst g = H.e
    @[hott] def ker_is_prop (x : G.carrier) : prop (ker.aux φ x) :=
    begin intros f g, apply H.hset end

    @[hott] def ker : G.subgroup :=
    pregroup.subgroup.mk ⟨ker.aux φ, ker_is_prop φ⟩
      (homo_unit φ)
      (begin
        intros a b h g, change _ = _,
        transitivity, { apply homo_mul }, symmetry,
        transitivity, { apply unit_sqr },
        apply equiv.bimap H.φ (Id.inv h) (Id.inv g)
      end)
      (begin
        intros x h, change _ = _,
        cases φ with φ p, calc
          φ x⁻¹ = H.ι (φ x) : homo_inv ⟨φ, p⟩ x
            ... = H.ι H.e   : H.ι # h
            ... = H.e       : Id.inv unit_inv
      end)

    def Ker := (ker φ).set.subtype

    @[hott] instance ker_is_normal_subgroup : G ⊵ ker φ :=
    begin
      apply is_normal_subgroup.mk, intros n g p, cases φ with φ q,
      change _ = _ at p, have r := Id.inv (homo_mul ⟨φ, q⟩ n g) ⬝ p, calc
        φ (g * n) = φ g × φ n       : homo_mul ⟨φ, q⟩ g n
              ... = φ g × H.ι (φ g) : (λ y, φ g × y) # (eq_inv_of_mul_eq_one r)
              ... = H.e             : group.mul_right_inv _
    end

    def im.carrier := (im φ.fst).subtype

    @[hott] def im : H.subgroup :=
    pregroup.subgroup.mk (im φ.fst)
      (HITs.merely.elem ⟨e, homo_unit φ⟩)
      (begin
        intros a b p q, fapply HITs.merely.rec _ _ p,
        { apply HITs.merely.uniq },
        { intro r,
          { fapply HITs.merely.rec _ _ q,
            { apply HITs.merely.uniq },
            { intro s, induction r with x r,
              induction s with y s,
              apply HITs.merely.elem,
              existsi (x * y), transitivity, apply homo_mul,
              induction r, induction s, trivial } } }
      end)
      (begin
        intros x p, fapply HITs.merely.rec _ _ p,
        { apply HITs.merely.uniq },
        { intro q, apply HITs.merely.elem,
          induction q with y q, existsi y⁻¹,
          transitivity, apply homo_inv,
          apply map, assumption }
      end)
  end

  @[hott] def zentrum (G : pregroup.{u}) [group G] : G.subgroup :=
  begin
    fapply pregroup.subgroup.mk,
    exact ⟨λ z, Π g, G.φ z g = G.φ g z, begin
      intros x p q, apply theorems.funext,
      intro y, apply G.hset
    end⟩,
    { intro x, transitivity,
      { apply G.one_mul },
      { symmetry, apply G.mul_one } },
    { intros a b g h c, symmetry, calc
        c * (a * b) = (c * a) * b : Id.inv (G.mul_assoc _ _ _)
                ... = (a * c) * b : (* b) # (Id.inv $ g c)
                ... = a * (c * b) : G.mul_assoc _ _ _
                ... = a * (b * c) : (G.φ a) # (Id.inv $ h c)
                ... = a * b * c   : Id.inv (G.mul_assoc _ _ _) },
    { intros a g b, calc
      a⁻¹ * b = a⁻¹ * b⁻¹⁻¹ : (G.φ a⁻¹) # (Id.inv $ inv_inv b)
          ... = (b⁻¹ * a)⁻¹ : Id.inv (inv_explode _ _)
          ... = (a * b⁻¹)⁻¹ : G.ι # (Id.inv $ g b⁻¹)
          ... = b⁻¹⁻¹ * a⁻¹ : inv_explode _ _
          ... = b * a⁻¹     : (* a⁻¹) # (inv_inv b) }
  end

  @[hott] instance zentrum_is_normal : G ⊵ zentrum G :=
  begin
    split, intros g h r z,
    have p := Id.inv (G.mul_assoc g h g) ⬝ r g,
    have q := mul_cancel_left p,
    transitivity, { apply map (* z), apply q },
    symmetry, transitivity, { apply map (G.φ z), apply q },
    symmetry, apply r
  end

  @[hott] def triv (G : pregroup) [group G] : G.subgroup :=
  begin
    fapply pregroup.subgroup.mk,
    exact ⟨λ x, G.e = x, begin intro x, apply G.hset end⟩,
    { change _ = _, reflexivity },
    { intros a b p q, change _ = _ at p, change _ = _ at q,
      induction p, induction q, change _ = _, symmetry, apply G.mul_one },
    { intros a p, change _ = _ at p, induction p, change _ = _, apply unit_inv }
  end

  @[hott] instance triv.normal_subgroup : G ⊵ triv G :=
  begin
    split, intros g h p, change _ = _ at p,
    change _ = _, apply @mul_cancel_left G _ _ _ g,
    transitivity, apply G.mul_one,
    transitivity, { symmetry, apply G.one_mul },
    symmetry, transitivity, { symmetry, apply G.mul_assoc },
    symmetry, apply Id.map (* g), assumption
  end

  @[hott] def univ (G : pregroup) : G.subgroup :=
  begin
    fapply pregroup.subgroup.mk, exact G.univ,
    all_goals { intros; apply ★ }
  end

  @[hott] instance univ_is_normal : G ⊵ univ G :=
  begin split, intros g h p, apply ★ end

  @[hott] def univ_iso (G : pregroup) [group G] : G ≅ Subgroup G (univ G) :=
  begin
    fapply mkiso, { intro x, existsi x, exact ★ },
    { intros x y, reflexivity }, apply types.qinv.to_biinv,
    fapply sigma.mk, { apply sigma.fst }, split; intro x,
    { induction x with x z, induction z, reflexivity }, { reflexivity }
  end

  @[hott] def intersect (φ ψ : G.subgroup) : G.subgroup :=
  begin
    fapply pregroup.subgroup.mk, exact (ens.inter φ.set ψ.set),
    { split, apply φ.unit, apply ψ.unit },
    { intros a b p q,
      induction p with p₁ p₂,
      induction q with q₁ q₂,
      split, apply φ.mul; assumption,
      apply ψ.mul; assumption },
    { intros a h, induction h with u v,
      split, apply φ.inv, assumption,
      apply ψ.inv, assumption }
  end

  @[hott] def mul (φ ψ : G.subset) : G.subset :=
  ⟨λ a, ∥(Σ x y, x ∈ φ × y ∈ ψ × x * y = a)∥, λ _, HITs.merely.uniq⟩
end group

end ground_zero.algebra