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
  variable {G : Group}

  local infixl:70 (priority := high) " * " => G.φ
  local postfix:max (priority := high) "⁻¹" => G.ι
  local notation "e" => G.e

  local infix:70 (priority := high) " ^ " => conjugate (G := G)
  local infix:70 (priority := high) " / " => rightDiv (G := G)

  hott def isNormal (G : Group) (φ : G.subset) :=
  Π g h, G.φ g h ∈ φ → G.φ h g ∈ φ

  notation:50 φ " ⊴ " G => isNormal G (subgroup.set φ)
  notation:50 G " ⊵ " φ => isNormal G (subgroup.set φ)

  hott def normal (G : Group) := Σ (φ : G.subgroup), G ⊵ φ

  hott def normal.set {G : Group} (φ : G.normal) := φ.1.set

  hott def isSubgroup.prop (φ : G.subset) : prop (G.isSubgroup φ) :=
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

  hott def isNormal.prop (φ : G.subset) : prop (G.isNormal φ) :=
  begin
    apply piProp; intro;
    apply piProp; intro;
    apply piProp; intro;
    apply Ens.prop
  end

  hott def subgroup.ext {φ ψ : G.subgroup} (ρ : φ.set = ψ.set) : φ = ψ :=
  begin fapply Sigma.prod; exact ρ; apply isSubgroup.prop end

  hott def normal.ext {φ ψ : G.normal} (ρ : φ.set = ψ.set) : φ = ψ :=
  begin fapply Sigma.prod; apply subgroup.ext ρ; apply isNormal.prop end

  hott def isNormalSubgroup.conj {φ : G.subgroup} (H : G ⊵ φ)
    (n g : G.carrier) : n ∈ φ.set → (n ^ g) ∈ φ.set :=
  begin
    intro h; change (g⁻¹ * n * g) ∈ φ.set; apply transport (· ∈ φ.set);
    { symmetry; apply G.mulAssoc }; apply H;
    apply transport (· ∈ φ.set); apply cancelRight; assumption
  end

  hott def conjugateEqv {φ : G.subgroup} (H : G ⊵ φ) (n g : G.carrier) :
    @conjugate G n g ∈ φ.set → @conjugateRev G n g ∈ φ.set :=
  begin
    intro h; apply H;
    apply transport (· ∈ φ.set); apply calc
      g * (g⁻¹ * n) = (g * g⁻¹) * n : Id.inv (G.mulAssoc g g⁻¹ n)
                ... = e * n         : Id.map (G.φ · n) (mulRightInv g)
                ... = (g⁻¹ * g) * n : Id.map (G.φ · n) (Id.inv (G.mulLeftInv g))
                ... = g⁻¹ * (g * n) : G.mulAssoc g⁻¹ g n;
    apply H; assumption
  end

  hott def normalSubgroupCosets {φ : G.subgroup} (H : G ⊵ φ) {x y : G.carrier} : ldiv φ x y ↔ rdiv φ x y :=
  begin
    apply Prod.mk <;> intro h;
    { change (x * y⁻¹) ∈ φ.set; apply transport (· ∈ φ.set);
      apply calc x * (y⁻¹ * x) * x⁻¹ = x * (y⁻¹ * x * x⁻¹) : G.mulAssoc x (leftDiv y x) x⁻¹
                                 ... = x * y⁻¹             : Id.map (G.φ x) (Id.inv (cancelRight y⁻¹ x));
      apply conjugateEqv H;
      apply isNormalSubgroup.conj H;
      apply transport (· ∈ φ.set); apply invMulInv;
      apply φ.inv; assumption };
    { change (x⁻¹ * y) ∈ φ.set; apply transport (· ∈ φ.set);
      apply calc x⁻¹ * (y * x⁻¹) * x = x⁻¹ * (y * x⁻¹ * x) : G.mulAssoc x⁻¹ (y / x) x
                                 ... = x⁻¹ * y             : Id.map (G.φ x⁻¹) (Id.inv (cancelLeft y x));
      apply isNormalSubgroup.conj H; apply transport (· ∈ φ.set);
      apply mulInvInv; apply φ.inv; assumption }
  end

  noncomputable hott def cosetsEq {φ : G.subgroup} (H : G ⊵ φ) : ldiv φ = rdiv φ :=
  begin
    apply Theorems.funext; intro; apply Theorems.funext; intro;
    apply ua.propext; apply Ens.prop; apply Ens.prop;
    apply normalSubgroupCosets H
  end

  section
    variable {H : Group.{u}} {φ : Group.subgroup.{u, v} H}

    hott def Subgroup.mul (x y : φ.subtype) : φ.subtype :=
    begin existsi H.φ x.1 y.1; apply φ.mul; apply x.2; apply y.2 end
    local infixl:70 " ∗ " => Subgroup.mul (H := H) (φ := φ)

    hott def Subgroup.inv (x : φ.subtype) : φ.subtype :=
    begin existsi H.ι x.1; apply φ.inv; apply x.2 end
    local postfix:80 (priority := high) "⁻¹" => Subgroup.inv (H := H) (φ := φ)

    hott def Subgroup.unit : φ.subtype := ⟨H.e, φ.unit⟩
    local notation "e" => Subgroup.unit (H := H) (φ := φ)

    hott def Subgroup.set : Structures.hset φ.subtype :=
    begin apply Ens.hset; apply Alg.hset end

    hott def Subgroup.mulAssoc (x y z : φ.subtype) : (x ∗ y) ∗ z = x ∗ (y ∗ z) :=
    begin fapply Types.Sigma.prod; apply H.mulAssoc; apply Ens.prop end

    hott def Subgroup.oneMul (x : φ.subtype) : e ∗ x = x :=
    begin fapply Types.Sigma.prod; apply H.oneMul; apply Ens.prop end

    hott def Subgroup.mulOne (x : φ.subtype) : x ∗ e = x :=
    begin fapply Types.Sigma.prod; apply H.mulOne; apply Ens.prop end

    hott def Subgroup.mulLeftInv (x : φ.subtype) : x⁻¹ ∗ x = e :=
    begin fapply Types.Sigma.prod; apply H.mulLeftInv; apply Ens.prop end

    hott def Subgroup (H : Group) (φ : H.subgroup) : Group :=
    @Group.intro φ.subtype Subgroup.set Subgroup.mul Subgroup.inv Subgroup.unit
      Subgroup.mulAssoc Subgroup.oneMul Subgroup.mulOne Subgroup.mulLeftInv
  end

  hott def Subgroup.ext : Π (φ ψ : G.subgroup), φ.set = ψ.set → Subgroup G φ = Subgroup G ψ :=
  begin intro ⟨φ, p⟩ ⟨ψ, q⟩ r; apply Id.map (Subgroup G); apply subgroup.ext r end

  hott def inter (φ ψ : G.subgroup) : subgroup (Subgroup G ψ) :=
  begin
    fapply Group.subgroup.mk;
    exact ⟨λ x, x.fst ∈ φ.set, λ x, Ens.prop x.fst φ.set⟩;
    { change e ∈ φ.set; apply φ.unit };
    { intro ⟨a, g⟩ ⟨b, h⟩ G H; change _ ∈ φ.set;
      apply φ.mul <;> assumption };
    { intro ⟨a, g⟩ G; change _ ∈ φ.set;
      apply φ.inv; assumption }
  end

  hott def abelianSubgroupIsNormal (G : Group) (ρ : G.isCommutative) (φ : G.subgroup) : G ⊵ φ :=
  begin intros g h p; apply transport (· ∈ φ.set); apply ρ; assumption end

  hott def abelianSubgroupIsAbelian (G : Group) (ρ : G.isCommutative)
    (φ : G.subgroup) : (Subgroup G φ).isCommutative :=
  begin intro ⟨a, p⟩ ⟨b, q⟩; fapply Sigma.prod; apply ρ; apply Ens.prop end

  hott def Hom.surj (φ : G.subgroup) : Hom (Subgroup G φ) G :=
  mkhomo Sigma.fst (λ ⟨a, _⟩ ⟨b, _⟩, idp (a * b))

  section
    variable {H : Group} (φ : Hom G H)
    local infixl:70 " ∗ " => H.φ

    hott def ker.aux := λ g, φ.fst g = H.e
    hott def kerIsProp (x : G.carrier) : prop (ker.aux φ x) := H.hset _ _

    hott def ker : G.normal :=
    ⟨Group.subgroup.mk ⟨ker.aux φ, kerIsProp φ⟩
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
      end),
    begin
      intro n g p; have r := Id.inv (homoMul φ n g) ⬝ p; apply calc
        φ.1 (g * n) = φ.1 g ∗ φ.1 n       : homoMul φ g n
                ... = φ.1 g ∗ H.ι (φ.1 g) : Id.map (H.φ (φ.1 g)) (eqInvOfMulEqOne r)
                ... = H.e                 : Group.mulRightInv _
    end⟩

    hott def Ker := (ker φ).set.subtype

    hott def im.carrier := (im φ.fst).subtype

    hott def im : H.subgroup :=
    Group.subgroup.mk (Algebra.im φ.1)
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

  hott def zentrum (G : Group.{u}) : G.normal :=
  ⟨begin
    fapply @Group.subgroup.mk G;
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
  end,
  begin
    intros g h r z;
    have p := Id.inv (G.mulAssoc g h g) ⬝ r g;
    have q := mulCancelLeft p;
    transitivity; apply Id.map (G.φ · z); apply q ;
    symmetry; transitivity; apply Id.map (G.φ z);
    apply q; symmetry; apply r
  end⟩

  hott def triv (G : Group) : G.normal :=
  ⟨begin
    fapply Group.subgroup.mk;
    exact ⟨λ x, G.e = x, λ _, G.hset _ _⟩;
    { change _ = _; reflexivity };
    { intro a b (p : _ = _) (q : _ = _);
      induction p; induction q;
      change _ = _; symmetry; apply G.mulOne };
    { intro a (p : _ = _); induction p;
      change _ = _; apply unitInv }
  end,
  begin
    intro g h (p : _ = _);
    change _ = _; apply G.mulCancelLeft;
    transitivity; apply G.mulOne;
    transitivity; symmetry; apply G.oneMul;
    symmetry; transitivity; symmetry; apply G.mulAssoc;
    symmetry; apply Id.map (G.φ · g); assumption
  end⟩

  hott def univ (G : Group) : G.normal :=
  ⟨begin fapply Group.subgroup.mk; exact Ens.univ G.carrier; all_goals { intros; apply ★ } end,
   begin intros g h p; apply ★ end⟩

  instance : Coe G.normal G.subgroup := ⟨Sigma.fst⟩

  hott def univIso (G : Group) : G ≅ Subgroup G (univ G) :=
  begin
    fapply mkiso; { intro x; existsi x; exact ★ };
    { intros x y; reflexivity }; apply Types.Qinv.toBiinv;
    fapply Sigma.mk; apply Sigma.fst; apply Prod.mk;
    { intro ⟨_, _⟩; reflexivity }; { reflexivity }
  end

  hott def intersect (φ ψ : G.subgroup) : G.subgroup :=
  begin
    fapply Group.subgroup.mk; exact (Ens.inter φ.set ψ.set);
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