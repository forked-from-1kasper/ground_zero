import GroundZero.Algebra.Group.Subgroup
import GroundZero.HITs.Quotient

open GroundZero.Types.Equiv (biinv transport)
open GroundZero.Types.Id (map)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero

/- Factor/Quotient group (as Quotient type). -/

namespace GroundZero.Algebra
universe u v u' v' w

namespace Group
  variable {G : Group}

  local infixl:70 (priority := high) " * " => G.φ
  local postfix:max (priority := high) "⁻¹" => G.ι
  local notation "e" => G.e

  hott def factorLeftRel (φ : G.subgroup) :
    G.carrier → G.carrier → Ω :=
  λ x y, ⟨ldiv φ x y, Ens.prop _ _⟩

  hott def factorRightRel (φ : G.subgroup) :
    G.carrier → G.carrier → Ω :=
  λ x y, ⟨rdiv φ x y, Ens.prop _ _⟩

  hott def factorEqrelLeft (φ : G.subgroup) : eqrel G.carrier :=
  ⟨factorLeftRel φ,
  begin
    apply Prod.mk;
    { intro; apply transport (· ∈ φ.set); symmetry;
      apply G.mulLeftInv; apply φ.unit }; apply Prod.mk;
    { intros x y h; apply transport (· ∈ φ.set);
      apply invMulInv; apply φ.inv; assumption };
    { intros x y z h g; apply transport (· ∈ φ.set);
      apply chainLdiv x y z; apply φ.mul <;> assumption }
  end⟩

  hott def factorEqrelRight (φ : G.subgroup) : eqrel G.carrier :=
  ⟨factorRightRel φ,
  begin
    apply Prod.mk;
    { intro; apply transport (· ∈ φ.set); symmetry;
      apply Group.mulRightInv; apply φ.unit }; apply Prod.mk;
    { intros x y h; apply transport (· ∈ φ.set);
      apply mulInvInv; apply φ.inv; assumption };
    { intros x y z h g; apply transport (· ∈ φ.set);
      apply chainRdiv x y z; apply φ.mul <;> assumption }
  end⟩

  def factorLeft (G : Group) (φ : G.subgroup) :=
  HITs.Quotient (factorEqrelLeft φ)

  def factorRight (G : Group) (φ : G.subgroup) :=
  HITs.Quotient (factorEqrelRight φ)

  noncomputable hott def factorSymm (φ : G.subgroup) (ρ : G ⊵ φ) :
    factorLeft G φ = factorRight G φ :=
  begin
    apply map GroundZero.HITs.Quotient; apply GroundZero.eqrel.eq;
    apply Theorems.funext; intro; apply Theorems.funext; intro;
    fapply Types.Sigma.prod; change ldiv φ _ _ = rdiv φ _ _;
    apply HITs.Interval.happly; apply HITs.Interval.happly;
    apply cosetsEq ρ; apply propIsProp
  end

  hott def Factor.incl {φ : G.subgroup} : G.carrier → factorLeft G φ :=
  GroundZero.HITs.Quotient.elem

  section
    variable {φ : G.normal}

    noncomputable hott def Factor.mul :
      factorLeft G φ → factorLeft G φ → factorLeft G φ :=
    begin
      fapply GroundZero.HITs.Quotient.lift₂;
      { intros a b; exact Factor.incl (a * b) };
      { apply GroundZero.HITs.Quotient.set };
      { intros a b c d p q;
        apply GroundZero.HITs.Quotient.sound;
        change _ ∈ φ.set; apply transport (· ∈ φ.set);
        apply calc
             b⁻¹ * (a⁻¹ * c * (d * b⁻¹)) * b
           = b⁻¹ * (a⁻¹ * c * d * b⁻¹) * b :
             Id.map (b⁻¹ * · * b) (Id.inv (G.mulAssoc (a⁻¹ * c) d b⁻¹))
       ... = b⁻¹ * (a⁻¹ * c * d * b⁻¹ * b) :
             G.mulAssoc b⁻¹ (a⁻¹ * c * d * b⁻¹) b
       ... = b⁻¹ * (a⁻¹ * c * d * (b⁻¹ * b)) :
             Id.map (G.φ b⁻¹) (G.mulAssoc (a⁻¹ * c * d) b⁻¹ b)
       ... = b⁻¹ * (a⁻¹ * c * d * e) :
             @map G.carrier G.carrier _ _ (λ x, b⁻¹ * (a⁻¹ * c * d * x)) (G.mulLeftInv b)
       ... = b⁻¹ * (a⁻¹ * c * d) :
             Id.map (b⁻¹ * ·) (G.mulOne (a⁻¹ * c * d))
       ... = b⁻¹ * (a⁻¹ * (c * d)) :
             Id.map (b⁻¹ * ·) (G.mulAssoc a⁻¹ c d)
       ... = (b⁻¹ * a⁻¹) * (c * d) :
             Id.inv (G.mulAssoc b⁻¹ a⁻¹ (c * d))
       ... = leftDiv (a * b) (c * d) :
             Id.map (G.φ · (c * d)) (Id.inv (invExplode a b));
        apply isNormalSubgroup.conj φ.2; apply φ.1.mul;
        { exact p };
        { apply transport (· ∈ φ.set); apply calc
            (b * d⁻¹)⁻¹ = d⁻¹⁻¹ * b⁻¹ : invExplode b d⁻¹
                    ... = d * b⁻¹     : Id.map (G.φ · b⁻¹) (invInv d);
          apply φ.1.inv; apply (normalSubgroupCosets φ.2).left; exact q } }
    end

    hott def Factor.one : factorLeft G φ := Factor.incl e

    noncomputable hott def Factor.mulOne : Π (x : factorLeft G φ), Factor.mul x Factor.one = x :=
    begin
      fapply @HITs.Quotient.indProp;
      { intro x; apply HITs.Quotient.sound;
        apply transport (· ∈ φ.set); apply calc
            e = x⁻¹ * x       : Id.inv (G.mulLeftInv x)
          ... = e * x⁻¹ * x   : Id.map (G.φ · x) (Id.inv (G.oneMul x⁻¹))
          ... = e⁻¹ * x⁻¹ * x : Id.map (λ y, y * x⁻¹ * x) unitInv
          ... = (x * e)⁻¹ * x : Id.map (G.φ · x) (Id.inv (invExplode x e));
        apply φ.1.unit };
      { intros; apply HITs.Quotient.set }
    end

    noncomputable hott def Factor.oneMul : Π (x : factorLeft G φ), Factor.mul Factor.one x = x :=
    begin
      fapply HITs.Quotient.indProp;
      { intro; change HITs.Quotient.elem _ = _;
        apply map; apply G.oneMul };
      { intros; apply HITs.Quotient.set }
    end

    noncomputable hott def Factor.assoc : Π (x y z : factorLeft G φ),
      Factor.mul (Factor.mul x y) z = Factor.mul x (Factor.mul y z) :=
    begin
      intro (x : HITs.Quotient _) (y : HITs.Quotient _) (z : HITs.Quotient _);
      induction x; induction y; induction z;
      apply Id.map Factor.incl; apply G.mulAssoc;
      -- ???
      apply HITs.Quotient.set; apply propIsSet; apply HITs.Quotient.set;
      apply HITs.Quotient.set; apply propIsSet; apply HITs.Quotient.set;
      apply HITs.Quotient.set; apply propIsSet; apply HITs.Quotient.set
    end

    noncomputable hott def Factor.inv : factorLeft G φ → factorLeft G φ :=
    begin
      fapply GroundZero.HITs.Quotient.rec;
      { intro x; exact Factor.incl x⁻¹ };
      { intros u v H; apply GroundZero.HITs.Quotient.sound;
        apply transport (· ∈ φ.set); symmetry;
        apply map (G.φ · v⁻¹); apply invInv;
        apply (normalSubgroupCosets φ.2).left; exact H };
      { apply GroundZero.HITs.Quotient.set }
    end

    noncomputable hott def Factor.leftInv :
      Π (x : factorLeft G φ), Factor.mul (Factor.inv x) x = Factor.one :=
    begin
      intro (x : HITs.Quotient _); induction x;
      apply Id.map Factor.incl; apply G.mulLeftInv;
      apply HITs.Quotient.set; apply propIsSet; apply HITs.Quotient.set
    end
  end

  section
    variable (H : Group) (φ : H.normal)

    noncomputable hott def Factor : Group :=
    @Group.intro (factorLeft H φ) HITs.Quotient.set Factor.mul Factor.inv Factor.one
      Factor.assoc Factor.oneMul Factor.mulOne Factor.leftInv
  end

  infix:70 " \\ " => Factor

  hott def Factor.sound {φ : G.normal} {x : G.carrier} (H : x ∈ φ.set) :
    @Id (factorLeft G φ) (Factor.incl x) Factor.one :=
  begin
    apply HITs.Quotient.sound; apply transport (· ∈ φ.set);
    symmetry; apply ldivByUnit; apply φ.1.inv; assumption
  end

  hott def Factor.lift {H : Group} (f : Hom G H) {φ : G.normal}
    (p : Π x, x ∈ φ.set → f.fst x = H.e) : factorLeft G φ → H.carrier :=
  begin
    fapply HITs.Quotient.rec; exact f.1;
    { intros x y q; apply eqOfDivEq; change H.φ _ _ = _;
      transitivity; apply Id.map (H.φ · (f.1 y));
      symmetry; apply homoInv f; transitivity;
      symmetry; apply homoMul; apply p; apply q };
    apply H.hset
  end

  hott def triv.encode : G.carrier → factorLeft G (triv G) := Factor.incl

  hott def triv.decode : factorLeft G (triv G) → G.carrier :=
  begin
    fapply HITs.Quotient.rec; exact id;
    { intro x y (p : _ = _); apply invInj;
      apply eqInvOfMulEqOne; exact Id.inv p };
    apply G.hset
  end

  noncomputable hott def triv.factor : G ≅ G\triv G :=
  begin
    fapply mkiso; exact triv.encode;
    { intros x y; reflexivity };
    apply Prod.mk <;> existsi triv.decode;
    { intro; reflexivity };
    { fapply HITs.Quotient.indProp <;> intro;
      reflexivity; apply HITs.Quotient.set }
  end

  hott def univ.decode : 𝟏 → factorLeft G (univ G) := λ _, Factor.one

  noncomputable hott def univContr :
    contr (factorLeft G (univ G)) :=
  begin
    existsi univ.decode.{_, 1, 1} ★;
    fapply HITs.Quotient.indProp <;> intro;
    { apply HITs.Quotient.sound; apply ★ };
    { apply HITs.Quotient.set }
  end

  noncomputable hott def univProp : prop (factorLeft G (univ G)) :=
  contrImplProp univContr

  noncomputable hott def univFactor : Z₁ ≅ G\univ G :=
  begin
    fapply mkiso; exact univ.decode; intros a b; apply univProp;
    apply Prod.mk <;> existsi (λ _, ★) <;> intro;
    apply unitIsProp; apply univProp
  end

  section
    variable {φ : G.normal} {ψ : G.normal}

    noncomputable hott def Factor.transfer (f : φ.set ⊆ ψ.set) : (G\φ).carrier → (G\ψ).carrier :=
    begin
      fapply HITs.Quotient.rec;
      { exact Factor.incl };
      { intros x y H; apply HITs.Quotient.sound; apply f; exact H };
      { apply HITs.Quotient.set }
    end

    noncomputable hott def Factor.iso (f : φ.set ⊆ ψ.set) (g : ψ.set ⊆ φ.set) : G\φ ≅ G\ψ :=
    begin
      fapply mkiso; exact Factor.transfer f;
      { intro (x : HITs.Quotient _) (y : HITs.Quotient _);
        induction x; induction y; reflexivity;
        apply HITs.Quotient.set; apply propIsSet; apply HITs.Quotient.set;
        apply HITs.Quotient.set; apply propIsSet; apply HITs.Quotient.set };
      { apply Prod.mk <;> existsi Factor.transfer g <;> fapply HITs.Quotient.indProp;
        -- “repeat” don’t work here too
        intro; reflexivity; intros; apply HITs.Quotient.set;
        intro; reflexivity; intros; apply HITs.Quotient.set }
    end
  end
end Group

end GroundZero.Algebra