import GroundZero.Algebra.Group.Basic

open GroundZero.Types.Equiv (biinv transport)
open GroundZero.Types.Id (map)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero

/-
  Kernel and image of homomorphism.
  Subgroup, normal subgroup.
-/

namespace GroundZero.Algebra

namespace Group
  open GroundZero.Algebra.Pregroup (rightDiv leftDiv conjugate conjugateRev subgroup)

  variable {G : Pregroup} [group G]

  local infixl:70 (priority := high) " * " => G.φ
  local postfix:max (priority := high) "⁻¹" => G.ι
  local notation "e" => G.e

  local infix:70 (priority := high) " ^ " => conjugate (G := G)
  local infix:70 (priority := high) " / " => rightDiv (G := G)

  hott def normal (G : Pregroup) (φ : G.subset) :=
  Π g h, G.φ g h ∈ φ → G.φ h g ∈ φ

  class isNormalSubgroup (G : Pregroup) (φ : G.subgroup) :=
  (cosetsEqv : normal G φ.set)

  notation:50 φ " ⊴ " G => isNormalSubgroup G φ
  infix:50 " ⊵ " => isNormalSubgroup

  hott def isSubgroup.prop (φ : G.subset) : prop (Pregroup.isSubgroup G φ) :=
  begin
    apply productProp; apply Ens.prop; apply productProp;
    -- TODO: fix “repeat” to able handle this case
    { apply piProp; intro;
      apply piProp; intro;
      apply piProp; intro;
      apply piProp; intro;
      apply Ens.prop };
    { apply piProp; intro;
      apply piProp; intro;
      apply Ens.prop };
  end

  hott def subgroup.ext : Π {φ ψ : G.subgroup}, φ.set = ψ.set → φ = ψ :=
  begin
    intro ⟨φ, p⟩ ⟨ψ, q⟩ (r : φ = ψ); induction r;
    apply Id.map; apply isSubgroup.prop
  end

  hott def isNormalSubgroup.conj (φ : G.subgroup)
    [G ⊵ φ] (n g : G.carrier) : n ∈ φ.set → (n ^ g) ∈ φ.set :=
  begin
    intro h; change (g⁻¹ * n * g) ∈ φ.set; apply transport (· ∈ φ.set);
    { symmetry; apply G.mulAssoc }; apply isNormalSubgroup.cosetsEqv;
    apply transport (· ∈ φ.set); apply cancelRight; assumption
  end

  hott def conjugateEqv (φ : G.subgroup) [G ⊵ φ] (n g : G.carrier) :
    @conjugate G n g ∈ φ.set → @conjugateRev G n g ∈ φ.set :=
  begin
    intro h; apply isNormalSubgroup.cosetsEqv;
    apply transport (· ∈ φ.set); apply calc
      g * (g⁻¹ * n) = (g * g⁻¹) * n : Id.inv (G.mulAssoc g g⁻¹ n)
                ... = e * n         : Id.map (G.φ · n) (mulRightInv g)
                ... = (g⁻¹ * g) * n : Id.map (G.φ · n) (Id.inv (G.mulLeftInv g))
                ... = g⁻¹ * (g * n) : G.mulAssoc g⁻¹ g n;
    apply isNormalSubgroup.cosetsEqv; assumption
  end

  hott def normalSubgroupCosets (φ : G.subgroup) [G ⊵ φ] {x y : G.carrier} : ldiv φ x y ↔ rdiv φ x y :=
  begin
    apply Prod.mk <;> intro h;
    { change (x * y⁻¹) ∈ φ.set; apply transport (· ∈ φ.set);
      apply calc x * (y⁻¹ * x) * x⁻¹ = x * (y⁻¹ * x * x⁻¹) : G.mulAssoc x (leftDiv y x) x⁻¹
                                 ... = x * y⁻¹             : Id.map (G.φ x) (Id.inv (cancelRight y⁻¹ x));
      apply conjugateEqv;
      apply isNormalSubgroup.conj;
      apply transport (· ∈ φ.set); apply invMulInv;
      apply φ.inv; assumption };
    { change (x⁻¹ * y) ∈ φ.set; apply transport (· ∈ φ.set);
      apply calc x⁻¹ * (y * x⁻¹) * x = x⁻¹ * (y * x⁻¹ * x) : G.mulAssoc x⁻¹ (y / x) x
                                 ... = x⁻¹ * y             : Id.map (G.φ x⁻¹) (Id.inv (cancelLeft y x));
      apply isNormalSubgroup.conj; apply transport (· ∈ φ.set);
      apply mulInvInv; apply φ.inv; assumption }
  end

  noncomputable hott def cosetsEq (φ : G.subgroup) [G ⊵ φ] : ldiv φ = rdiv φ :=
  begin
    apply Theorems.funext; intro; apply Theorems.funext; intro;
    apply ua.propext; apply Ens.prop; apply Ens.prop;
    apply normalSubgroupCosets
  end

  section
    variable {H : Pregroup.{u}} {φ : Pregroup.subgroup.{u, v} H}

    hott def subgroup.mul (x y : φ.subtype) : φ.subtype :=
    begin existsi H.φ x.1 y.1; apply φ.mul; apply x.2; apply y.2 end
    local infixl:70 " ∗ " => subgroup.mul (H := H) (φ := φ)

    hott def subgroup.inv (x : φ.subtype) : φ.subtype :=
    begin existsi H.ι x.1; apply φ.inv; apply x.2 end
    local postfix:80 (priority := high) "⁻¹" => subgroup.inv (H := H) (φ := φ)

    hott def subgroup.unit : φ.subtype := ⟨H.e, φ.unit⟩
    local notation "e" => subgroup.unit (H := H) (φ := φ)

    hott def subgroup.set : hset φ.subtype :=
    begin apply Ens.hset; apply Alg.hset end

    hott def subgroup.mulAssoc [group H] (x y z : φ.subtype) : (x ∗ y) ∗ z = x ∗ (y ∗ z) :=
    begin fapply Types.Sigma.prod; apply H.mulAssoc; apply Ens.prop end

    hott def subgroup.oneMul [group H] (x : φ.subtype) : e ∗ x = x :=
    begin fapply Types.Sigma.prod; apply H.oneMul; apply Ens.prop end

    hott def subgroup.mulOne [group H] (x : φ.subtype) : x ∗ e = x :=
    begin fapply Types.Sigma.prod; apply H.mulOne; apply Ens.prop end

    hott def subgroup.mulLeftInv [group H] (x : φ.subtype) : x⁻¹ ∗ x = e :=
    begin fapply Types.Sigma.prod; apply group.mulLeftInv; apply Ens.prop end

    hott def Subgroup (H : Pregroup) (φ : H.subgroup) : Pregroup :=
    @Pregroup.intro φ.subtype subgroup.set subgroup.mul subgroup.inv subgroup.unit

    instance subgroup.semigroup [group H] : semigroup (Subgroup H φ).magma :=
    ⟨subgroup.mulAssoc⟩

    instance subgroup.monoid [group H] : monoid (Subgroup H φ).premonoid :=
    ⟨subgroup.semigroup, subgroup.oneMul, subgroup.mulOne⟩

    instance subgroup.group [group H] : group (Subgroup H φ) :=
    ⟨subgroup.monoid, subgroup.mulLeftInv⟩
  end

  hott def Subgroup.ext : Π (φ ψ : G.subgroup), φ.set = ψ.set → Subgroup G φ = Subgroup G ψ :=
  begin intro ⟨φ, p⟩ ⟨ψ, q⟩ r; apply Id.map (Subgroup G); apply subgroup.ext r end

  hott def inter (φ ψ : G.subgroup) : subgroup (Subgroup G ψ) :=
  begin
    fapply Pregroup.subgroup.mk;
    exact ⟨λ x, x.fst ∈ φ.set, λ x, Ens.prop x.fst φ.set⟩;
    { change e ∈ φ.set; apply φ.unit };
    { intro ⟨a, g⟩ ⟨b, h⟩ G H; change _ ∈ φ.set;
      apply φ.mul <;> assumption };
    { intro ⟨a, g⟩ G; change _ ∈ φ.set;
      apply φ.inv; assumption }
  end

  instance abelianSubgroupIsNormal (G : Pregroup) [abelian G] (φ : G.subgroup) : G ⊵ φ :=
  begin
    constructor; intros g h p; apply transport (· ∈ φ.set);
    apply Pregroup.mulComm; assumption
  end

  instance abelianSubgroupIsAbelian (G : Pregroup) [abelian G]
    (φ : G.subgroup) : abelian (Subgroup G φ) :=
  begin
    constructor; intro ⟨a, p⟩ ⟨b, q⟩; fapply Sigma.prod;
    apply Pregroup.mulComm G; apply Ens.prop
  end

  hott def homo.surj (φ : G.subgroup) : Subgroup G φ ⤳ G :=
  mkhomo Sigma.fst (λ ⟨a, _⟩ ⟨b, _⟩, idp (a * b))

  section
    variable {H : Pregroup} [group H] (φ : G ⤳ H)
    local infixl:70 " × " => H.φ

    hott def ker.aux := λ g, φ.fst g = H.e
    hott def kerIsProp (x : G.carrier) : prop (ker.aux φ x) := H.hset _ _

    hott def ker : G.subgroup :=
    Pregroup.subgroup.mk ⟨ker.aux φ, kerIsProp φ⟩
      (homoUnit φ)
      (begin
        intros a b h g; change _ = _;
        transitivity; apply homoMul; symmetry;
        transitivity; apply unitSqr;
        apply Equiv.bimap H.φ (Id.inv h) (Id.inv g)
      end)
      (begin
        intros x h; change _ = _;
        apply calc
          φ.1 x⁻¹ = H.ι (φ.1 x) : homoInv φ x
              ... = H.ι H.e     : Id.map H.ι h
              ... = H.e         : Id.inv unitInv
      end)

    hott def Ker := (ker φ).set.subtype

    instance kerIsNormalSubgroup : G ⊵ ker φ :=
    begin
      constructor; intro n g p; have r := Id.inv (homoMul φ n g) ⬝ p; apply calc
        φ.1 (g * n) = φ.1 g × φ.1 n       : homoMul φ g n
                ... = φ.1 g × H.ι (φ.1 g) : Id.map (H.φ (φ.1 g)) (eqInvOfMulEqOne r)
                ... = H.e                 : Group.mulRightInv _
    end

    hott def im.carrier := (im φ.fst).subtype

    hott def im : H.subgroup :=
    Pregroup.subgroup.mk (Algebra.im φ.1)
      (HITs.Merely.elem ⟨e, homoUnit φ⟩)
      (begin
        intro a b (p : ∥_∥); induction p; case elemπ p =>
        { intro (q : ∥_∥); induction q; case elemπ q =>
          { apply HITs.Merely.elem; existsi p.1 * q.1;
            transitivity; apply homoMul; apply Equiv.bimap H.φ;
            apply p.2; apply q.2 };
          apply HITs.Merely.uniq };
        apply piProp; intro; apply HITs.Merely.uniq
      end)
      (begin
        intro a (p : ∥_∥); induction p; case elemπ p =>
        { apply HITs.Merely.elem; existsi p.1⁻¹;
          transitivity; apply homoInv; apply map _ p.2 };
        apply HITs.Merely.uniq
      end)
  end

  hott def zentrum (G : Pregroup.{u}) [group G] : G.subgroup :=
  begin
    fapply @Pregroup.subgroup.mk G;
    exact ⟨λ z, Π g, G.φ z g = G.φ g z, begin
      intros x p q; apply Theorems.funext;
      intro y; apply G.hset
    end⟩;
    { intro; transitivity; apply G.oneMul; symmetry; apply G.mulOne };
    { intros a b g h c; symmetry; apply calc
        G.φ c (G.φ a b) = G.φ (G.φ c a) b : Id.inv (G.mulAssoc _ _ _)
                    ... = G.φ (G.φ a c) b : Id.map (G.φ · b) (Id.inv (g c))
                    ... = G.φ a (G.φ c b) : G.mulAssoc _ _ _
                    ... = G.φ a (G.φ b c) : Id.map (G.φ a) (Id.inv (h c))
                    ... = G.φ (G.φ a b) c : Id.inv (G.mulAssoc _ _ _) };
    { intros a g b; apply calc
      G.φ (G.ι a) b = G.φ (G.ι a) (G.ι (G.ι b)) : Id.map (G.φ (G.ι a)) (Id.inv (invInv b))
                ... = G.ι (G.φ (G.ι b) a)       : Id.inv (invExplode _ _)
                ... = G.ι (G.φ a (G.ι b))       : Id.map G.ι (Id.inv (g (G.ι b)))
                ... = G.φ (G.ι (G.ι b)) (G.ι a) : invExplode _ _
                ... = G.φ b (G.ι a)             : Id.map (G.φ · (G.ι a)) (invInv b) }
  end

  instance zentrumIsNormal : G ⊵ zentrum G :=
  begin
    constructor; intros g h r z;
    have p := Id.inv (G.mulAssoc g h g) ⬝ r g;
    have q := mulCancelLeft p;
    transitivity; apply Id.map (G.φ · z); apply q ;
    symmetry; transitivity; apply Id.map (G.φ z);
    apply q; symmetry; apply r
  end

  hott def triv (G : Pregroup) [group G] : G.subgroup :=
  begin
    fapply Pregroup.subgroup.mk;
    exact ⟨λ x, G.e = x, λ _, G.hset _ _⟩;
    { change _ = _; reflexivity };
    { intro a b (p : _ = _) (q : _ = _);
      induction p; induction q;
      change _ = _; symmetry; apply G.mulOne };
    { intro a (p : _ = _); induction p;
      change _ = _; apply unitInv }
  end

  instance triv.normal_subgroup : G ⊵ triv G :=
  begin
    constructor; intro g h (p : _ = _);
    change _ = _; apply @mulCancelLeft G _ _ _ g;
    transitivity; apply G.mulOne;
    transitivity; symmetry; apply G.oneMul;
    symmetry; transitivity; symmetry; apply G.mulAssoc;
    symmetry; apply Id.map (G.φ · g); assumption
  end

  hott def univ (G : Pregroup) : G.subgroup :=
  begin fapply Pregroup.subgroup.mk; exact G.univ; all_goals { intros; apply ★ } end

  instance univIsNormal : G ⊵ univ G :=
  begin constructor; intros g h p; apply ★ end

  hott def univIso (G : Pregroup) [group G] : G ≅ Subgroup G (univ G) :=
  begin
    fapply mkiso; { intro x; existsi x; exact ★ };
    { intros x y; reflexivity }; apply Types.Qinv.toBiinv;
    fapply Sigma.mk; apply Sigma.fst; apply Prod.mk;
    { intro ⟨_, _⟩; reflexivity }; { reflexivity }
  end

  hott def intersect (φ ψ : G.subgroup) : G.subgroup :=
  begin
    fapply Pregroup.subgroup.mk; exact (Ens.inter φ.set ψ.set);
    { apply Prod.mk; apply φ.unit; apply ψ.unit };
    { intro a b (p₁, p₂) (q₁, q₂); apply Prod.mk;
      apply φ.mul <;> assumption;
      apply ψ.mul <;> assumption };
    { intro a (p, q); apply Prod.mk;
      apply φ.inv; assumption;
      apply ψ.inv; assumption }
  end

  hott def mul (φ ψ : G.subset) : G.subset :=
  ⟨λ a, ∥(Σ x y, x ∈ φ × y ∈ ψ × x * y = a)∥, λ _, HITs.Merely.uniq⟩
end Group

end GroundZero.Algebra