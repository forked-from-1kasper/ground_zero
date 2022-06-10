import GroundZero.Theorems.Functions
import GroundZero.Algebra.Basic
open GroundZero.Types.Equiv (bimap biinv transport)
open GroundZero.Types.Id (map)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero

/-
  Basic lemmas about groups and abelian groups.

  Homomorphism properties.

  ℤ₁ and ℤ₂ groups.

  Opposite group.
  * https://en.wikipedia.org/wiki/Opposite_group
-/

namespace GroundZero.Algebra
universe u v u' v' w

section
  variable {μ : Type u} {η : Type v} (φ : μ → η)
  def im.aux := Theorems.Functions.fibInh φ
  def im : Ens η := ⟨im.aux φ, λ _, HITs.Merely.uniq⟩

  def im.intro (m : μ) : φ m ∈ im φ :=
  begin apply HITs.Merely.elem; existsi m; reflexivity end

  def im.inh (m : μ) : (im φ).inh :=
  begin apply HITs.Merely.elem; existsi φ m; apply im.intro end
end

namespace Group
  variable (G : Group)
  hott def isproper (x : G.carrier) := x ≠ G.e

  hott def proper := Σ x, G.isproper x

  hott def proper.prop {x : G.carrier} : prop (G.isproper x) :=
  Structures.implProp Structures.emptyIsProp

  hott def isSubgroup (φ : G.subset) :=
  (G.e ∈ φ) × (Π a b, a ∈ φ → b ∈ φ → G.φ a b ∈ φ) × (Π a, a ∈ φ → G.ι a ∈ φ)

  hott def subgroup := Σ φ, isSubgroup G φ
end Group

namespace Group
  variable {G : Group}
  def conjugate (a x : G.carrier) := G.φ (G.φ (G.ι x) a) x

  def conjugateRev (a x : G.carrier) := G.φ (G.φ x a) (G.ι x)

  def rightDiv (x y : G.carrier) := G.φ x (G.ι y)
  def leftDiv  (x y : G.carrier) := G.φ (G.ι x) y

  def subgroup.set (φ : G.subgroup) : Ens G.carrier := φ.1
  def subgroup.subtype (φ : G.subgroup) := φ.set.subtype

  def subgroup.mem (x : G.carrier) (φ : G.subgroup) := x ∈ φ.set

  def subgroup.ssubset (φ ψ : G.subgroup) :=
  Ens.ssubset φ.set ψ.set

  def subgroup.unit (φ : G.subgroup) := φ.2.1
  def subgroup.mul  (φ : G.subgroup) := φ.2.2.1
  def subgroup.inv  (φ : G.subgroup) := φ.2.2.2

  def subgroup.mk (φ : G.subset) (α : G.e ∈ φ)
    (β : Π a b, a ∈ φ → b ∈ φ → G.φ a b ∈ φ)
    (γ : Π a, a ∈ φ → G.ι a ∈ φ) : subgroup G :=
  ⟨φ, (α, β, γ)⟩
end Group

namespace Group
  variable {G : Group}

  local infixl:70 (priority := high) " * " => G.φ
  local postfix:max (priority := high) "⁻¹" => G.ι
  local notation "e" => G.e

  hott def leftUnitUniq (e' : G.carrier) (oneMul' : Π a, e' * a = a) : e' = e :=
  Id.inv (G.mulOne e') ⬝ oneMul' e

  hott def rightUnitUniq (e' : G.carrier) (mulOne' : Π a, a * e' = a) : e' = e :=
  Id.inv (G.oneMul e') ⬝ mulOne' e

  hott def unitOfSqr {x : G.carrier} (h : x * x = x) := calc
      x = e * x         : Id.inv (G.oneMul _)
    ... = (x⁻¹ * x) * x : Id.map (G.φ · x) (Id.inv (G.mulLeftInv x))
    ... = x⁻¹ * (x * x) : G.mulAssoc _ _ _
    ... = x⁻¹ * x       : Id.map (G.φ x⁻¹) h
    ... = e             : G.mulLeftInv _

  hott def invEqOfMulEqOne {x y : G.carrier} (h : x * y = e) := calc
     x⁻¹ = x⁻¹ * e       : Id.inv (G.mulOne _)
     ... = x⁻¹ * (x * y) : Id.map (G.φ x⁻¹) (Id.inv h)
     ... = (x⁻¹ * x) * y : Id.inv (G.mulAssoc _ _ _)
     ... = e * y         : Id.map (G.φ · y) (G.mulLeftInv x)
     ... = y             : G.oneMul y

  hott def invInv (x : G.carrier) : x⁻¹⁻¹ = x :=
  invEqOfMulEqOne (G.mulLeftInv x)

  hott def eqInvOfMulEqOne {x y : G.carrier} (h : x * y = e) : x = y⁻¹ :=
  Id.inv (invInv x) ⬝ Id.map G.ι (invEqOfMulEqOne h)

  hott def mulRightInv (x : G.carrier) := calc
    x * x⁻¹ = x⁻¹⁻¹ * x⁻¹ : Id.map (G.φ · x⁻¹) (Id.inv (invInv x))
        ... = e           : G.mulLeftInv x⁻¹

  hott def mulEqOneOfInvEq {x y : G.carrier} (h : x⁻¹ = y) : x * y = e :=
  Id.inv (Id.map (G.φ x) h) ⬝ (mulRightInv x)

  hott def invInj {x y : G.carrier} (h : x⁻¹ = y⁻¹) : x = y := calc
      x = x⁻¹⁻¹ : Id.inv (invInv x)
    ... = y⁻¹⁻¹ : Id.map G.ι h
    ... = y     : invInv y

  hott def mulCancelLeft {a b c : G.carrier} (h : c * a = c * b) := calc
      a = e * a         : Id.inv (G.oneMul a)
    ... = (c⁻¹ * c) * a : Id.map (G.φ · a) (Id.inv (G.mulLeftInv c))
    ... = c⁻¹ * (c * a) : G.mulAssoc _ _ _
    ... = c⁻¹ * (c * b) : Id.map (G.φ c⁻¹) h
    ... = (c⁻¹ * c) * b : Id.inv (G.mulAssoc _ _ _)
    ... = e * b         : Id.map (G.φ · b) (G.mulLeftInv c)
    ... = b             : G.oneMul b

  hott def mulCancelRight {a b c : G.carrier} (h : a * c = b * c) := calc
      a = a * e         : Id.inv (G.mulOne a)
    ... = a * (c * c⁻¹) : Id.map (G.φ a) (Id.inv (mulRightInv c))
    ... = (a * c) * c⁻¹ : Id.inv (G.mulAssoc _ _ _)
    ... = (b * c) * c⁻¹ : Id.map (G.φ · c⁻¹) h
    ... = b * (c * c⁻¹) : G.mulAssoc _ _ _
    ... = b * e         : Id.map (G.φ b) (mulRightInv c)
    ... = b             : G.mulOne b

  hott def unitInv : e = e⁻¹ :=
  Id.inv (mulRightInv e) ⬝ G.oneMul e⁻¹

  hott def unitSqr : e = e * e :=
  Id.inv (G.oneMul e)

  hott def unitCommutes (x : G.carrier) : e * x = x * e :=
  (G.oneMul x) ⬝ Id.inv (G.mulOne x)

  hott def unitCommutesInv (x : G.carrier) : x * e = e * x :=
  Id.inv (unitCommutes x)

  hott def invExplode (x y : G.carrier) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
  invEqOfMulEqOne
    (calc (x * y) * (y⁻¹ * x⁻¹)
        = ((x * y) * y⁻¹) * x⁻¹ : Id.inv (G.mulAssoc _ _ _)
    ... = (x * (y * y⁻¹)) * x⁻¹ : Id.map (G.φ · x⁻¹) (G.mulAssoc _ _ _)
    ... = (x * e) * x⁻¹         : Id.map (λ z, (x * z) * x⁻¹) (mulRightInv _)
    ... = x * x⁻¹               : Id.map (G.φ · x⁻¹) (G.mulOne x)
    ... = e                     : mulRightInv _)

  hott def sqrUnit {x : G.carrier} (p : x * x = e) := calc
      x = x * e         : Id.inv (G.mulOne x)
    ... = x * (x * x⁻¹) : Id.map (G.φ x) (Id.inv (mulRightInv x))
    ... = (x * x) * x⁻¹ : Id.inv (G.mulAssoc x x x⁻¹)
    ... = e * x⁻¹       : Id.map (G.φ · x⁻¹) p
    ... = x⁻¹           : G.oneMul x⁻¹

  hott def sqrUnitImplsAbelian (H : Π x, x * x = e) : G.isCommutative :=
  begin
    intros x y; have F := λ x, sqrUnit (H x); apply calc
      x * y = x⁻¹ * y⁻¹ : bimap G.φ (F x) (F y)
        ... = (y * x)⁻¹ : Id.inv (invExplode y x)
        ... = y * x     : Id.inv (F _)
  end

  local infix:70 (priority := high) " ^ " => conjugate (G := G)
  local infix:70 (priority := high) " / " => rightDiv (G := G)

  hott def eqOfDivEq {x y : G.carrier}
    (h : @leftDiv G x y = e) : x = y :=
  Id.inv (invInv x) ⬝ (invEqOfMulEqOne h)

  hott def eqOfRdivEq {x y : G.carrier} (h : x / y = e) : x = y :=
  invInj (invEqOfMulEqOne h)

  hott def cancelLeft (a b : G.carrier) := calc
      a = a * e         : Id.inv (G.mulOne a)
    ... = a * (b⁻¹ * b) : Id.map (G.φ a) (Id.inv (G.mulLeftInv b))
    ... = (a * b⁻¹) * b : Id.inv (G.mulAssoc a b⁻¹ b)

  hott def cancelRight (a b : G.carrier) := calc
      a = a * e         : Id.inv (G.mulOne a)
    ... = a * (b * b⁻¹) : Id.map (G.φ a) (Id.inv (mulRightInv b))
    ... = (a * b) * b⁻¹ : Id.inv (G.mulAssoc a b b⁻¹)

  hott def revCancelLeft (a b : G.carrier) := calc
      b = e * b         : Id.inv (G.oneMul b)
    ... = (a⁻¹ * a) * b : Id.map (G.φ · b) (Id.inv (G.mulLeftInv a))
    ... = a⁻¹ * (a * b) : G.mulAssoc a⁻¹ a b

  hott def revCancelRight (a b : G.carrier) := calc
      b = e * b         : Id.inv (G.oneMul b)
    ... = (a * a⁻¹) * b : Id.map (G.φ · b) (Id.inv (mulRightInv a))
    ... = a * (a⁻¹ * b) : G.mulAssoc a a⁻¹ b

  hott def commImplConj {x y : G.carrier} (p : x * y = y * x) : x = x ^ y := calc
      x = e * x         : Id.inv (G.oneMul x)
    ... = (y⁻¹ * y) * x : Id.map (G.φ · x) (Id.inv (G.mulLeftInv y))
    ... = y⁻¹ * (y * x) : G.mulAssoc y⁻¹ y x
    ... = y⁻¹ * (x * y) : Id.map (G.φ y⁻¹) (Id.inv p)
    ... = (y⁻¹ * x) * y : Id.inv (G.mulAssoc y⁻¹ x y)
    ... = x ^ y         : Id.refl

  hott def invEqOfMulRevEqOne {x y : G.carrier} (h : y * x = e) : x⁻¹ = y :=
  begin
    transitivity; apply eqInvOfMulEqOne (y := y⁻¹);
    transitivity; symmetry; apply invExplode;
    transitivity; apply Id.map G.ι; exact h;
    apply Id.inv unitInv; apply invInv
  end

  hott def isLeftInvertibleProp : prop (G.1.isLeftInvertible G.e) :=
  begin
    intro w₁ w₂; fapply Sigma.prod; fapply Theorems.funext; intro x;
    transitivity; apply eqInvOfMulEqOne; apply w₁.2;
    apply invEqOfMulRevEqOne; apply w₂.2;
    apply piProp; intro; apply G.hset
  end

  hott def isGroupProp : prop G.1.isGroup :=
  begin
    apply productProp; apply G.1.assocProp;
    apply sigProp; apply G.1.unitalProp;
    intro H; apply transport (λ g, prop (G.1.isLeftInvertible g));
    symmetry; apply leftUnitUniq; intro; apply (H.2 _).1;
    apply isLeftInvertibleProp
  end

  hott def isGroupPropMagma (M : Magma) : prop M.isGroup :=
  begin apply lemProp; intro H; apply @isGroupProp ⟨M, H⟩ end

  hott def commutator (x y : G.carrier) := (x * y) * (x⁻¹ * y⁻¹)

  hott def commutes {x y : G.carrier}
    (p : commutator x y = e) : x * y = y * x :=
  begin
    symmetry; transitivity; { symmetry; apply invInv };
    transitivity; apply Id.map; apply invExplode;
    symmetry; apply eqInvOfMulEqOne; exact p
  end

  hott def commutatorOverInv (x y : G.carrier) :
    (commutator x y)⁻¹ = commutator y x :=
  begin
    transitivity; apply invExplode;
    transitivity; apply Id.map; apply invExplode;
    apply Id.map (λ z, z * (y⁻¹ * x⁻¹)); transitivity; apply invExplode;
    transitivity; apply Id.map; apply invInv;
    apply Id.map (G.φ · x); apply invInv
  end

  def ldiv (φ : G.subgroup) := λ x y, @leftDiv G x y ∈ φ.set
  def rdiv (φ : G.subgroup) := λ x y, (x / y) ∈ φ.set

  hott def invMulInv (x y : G.carrier) := calc
    (x⁻¹ * y)⁻¹ = y⁻¹ * x⁻¹⁻¹ : invExplode _ _
            ... = y⁻¹ * x     : Id.map (G.φ y⁻¹) (invInv x)

  hott def mulInvInv (x y : G.carrier) := calc
    (x * y⁻¹)⁻¹ = y⁻¹⁻¹ * x⁻¹ : invExplode _ _
            ... = y * x⁻¹     : Id.map (G.φ · x⁻¹) (invInv y)

  hott def divByUnit (x : G.carrier) : x / e = x :=
  begin change _ * _ = _; transitivity; apply Id.map; symmetry; apply unitInv; apply G.mulOne end

  hott def ldivByUnit (x : G.carrier) : leftDiv x e = x⁻¹ :=
  by apply G.mulOne

  hott def chainLdiv (x y z : G.carrier) := calc
          (leftDiv x y) * (leftDiv y z)
        = (x⁻¹ * y) * (y⁻¹ * z) : Id.refl
    ... = x⁻¹ * (y * (y⁻¹ * z)) : G.mulAssoc x⁻¹ y (y⁻¹ * z)
    ... = x⁻¹ * ((y * y⁻¹) * z) : Id.map (G.φ x⁻¹) (Id.inv (G.mulAssoc y y⁻¹ z))
    ... = x⁻¹ * (e * z)         : Id.map (λ g, x⁻¹ * (g * z)) (mulRightInv _)
    ... = leftDiv x z           : Id.map (G.φ x⁻¹) (G.oneMul z)

  hott def chainRdiv (x y z : G.carrier) := calc
    (x / y) * (y / z) = (x * y⁻¹) * (y * z⁻¹) : Id.refl
                  ... = x * (y⁻¹ * (y * z⁻¹)) : G.mulAssoc x y⁻¹ (y * z⁻¹)
                  ... = x * ((y⁻¹ * y) * z⁻¹) : Id.map (G.φ x) (Id.inv (G.mulAssoc y⁻¹ y z⁻¹))
                  ... = x * (e * z⁻¹)         : Id.map (λ g, x * (g * z⁻¹)) (G.mulLeftInv _)
                  ... = x / z                 : Id.map (G.φ x) (G.oneMul z⁻¹)

  hott def conjugate.idem (x : G.carrier) := calc
    conjugate x x = G.φ G.e x : Id.map (G.φ · x) (G.mulLeftInv x)
              ... = x         : G.oneMul x

  hott def conjugate.eq {x y : G.carrier}
    (p : conjugate x y = y) : x = y :=
  begin
    symmetry; apply eqOfDivEq; fapply mulCancelRight; exact y;
    transitivity; exact p; symmetry; apply G.oneMul
  end

  hott def conjugate.comm {x y : G.carrier}
    (p : conjugate x y = x) : G.φ x y = G.φ y x :=
  begin
    fapply mulCancelLeft; exact G.ι y;
    transitivity; { symmetry; apply G.mulAssoc };
    transitivity; exact p; transitivity;
    { transitivity; symmetry; apply G.oneMul;
      apply Id.map (G.φ · x); symmetry; apply G.mulLeftInv y };
    apply G.mulAssoc
  end

  section
    variable {H K : Group}

    hott def homoMul (φ : Hom H K) (x y : H.carrier) :
      φ.1 (H.φ x y) = K.φ (φ.1 x) (φ.1 y) :=
    φ.2.1 ★ (x, y, ★)
  end

  section
    variable {H : Group}
    local infixl:70 " ∗ " => H.φ

    hott def homoRespectsUnit {φ : G.carrier → H.carrier}
      (p : Π a b, φ (a * b) = φ a ∗ φ b) : φ G.e = H.e :=
    begin
      apply unitOfSqr; apply calc
        H.φ (φ e) (φ e) = φ (G.e * G.e) : Id.inv (p G.e G.e)
                    ... = φ G.e         : Id.map φ (Id.inv unitSqr)
    end

    hott def homoRespectsInv {φ : G.carrier → H.carrier}
      (p : Π a b, φ (a * b) = φ a ∗ φ b) (x : G.carrier) : φ x⁻¹ = H.ι (φ x) := calc
        φ x⁻¹ = φ x⁻¹ ∗ H.e               : Id.inv (H.mulOne (φ x⁻¹))
          ... = φ x⁻¹ ∗ (φ x ∗ H.ι (φ x)) : Id.map (H.φ (φ x⁻¹)) (Id.inv (mulRightInv (φ x)))
          ... = φ x⁻¹ ∗ φ x ∗ H.ι (φ x)   : Id.inv (H.mulAssoc _ _ _)
          ... = φ (x⁻¹ * x) ∗ H.ι (φ x)   : Id.map (H.φ · (H.ι (φ x))) (Id.inv (p x⁻¹ x))
          ... = φ G.e ∗ H.ι (φ x)         : Id.map (λ y, φ y ∗ H.ι (φ x)) (G.mulLeftInv x)
          ... = H.e ∗ H.ι (φ x)           : Id.map (H.φ · (H.ι (φ x))) (homoRespectsUnit p)
          ... = H.ι (φ x)                 : H.oneMul (H.ι (φ x))

    hott def mkhomo (φ : G.carrier → H.carrier)
      (p : Π a b, φ (a * b) = φ a ∗ φ b) : Hom G H :=
    ⟨φ, (λ _ (x, y, _), p x y, λ z, nomatch z)⟩

    hott def mkiso (φ : G.carrier → H.carrier)
      (p : Π a b, φ (a * b) = φ a ∗ φ b) (q : biinv φ) : G ≅ H :=
    ⟨φ, ((mkhomo φ p).snd, q)⟩

    hott def homoUnit (φ : Hom G H) : φ.1 G.e = H.e :=
    homoRespectsUnit (homoMul φ)

    hott def homoInv (φ : Hom G H) : Π x, φ.1 (G.ι x) = H.ι (φ.1 x) :=
    homoRespectsInv (homoMul φ)

    hott def isoUnit (φ : G ≅ H) : φ.fst G.e = H.e :=
    homoUnit φ.hom

    hott def isoInv (φ : G ≅ H) : Π x, φ.fst x⁻¹ = H.ι (φ.fst x) :=
    homoInv φ.hom

    hott def isoMul (φ : G ≅ H) :
      Π x y, φ.fst (x * y) = φ.fst x ∗ φ.fst y :=
    homoMul φ.hom

    hott def homoRespectsDiv (φ : Hom G H) (x y : G.carrier) :
      φ.1 (x / y) = rightDiv (φ.1 x) (φ.1 y) := calc
      φ.1 (x / y) = φ.1 x ∗ φ.1 y⁻¹     : homoMul φ x y⁻¹
              ... = φ.1 x ∗ H.ι (φ.1 y) : Id.map (H.φ (φ.1 x)) (homoInv φ y)

    hott def Homo.zero : Hom G H :=
    mkhomo (λ _, H.e) (λ _ _, Id.inv (H.oneMul H.e))

    instance : OfNat (Hom G H) Nat.zero := ⟨Homo.zero⟩
    instance : OfNat (Algebra.Hom G.1 H.1) Nat.zero := ⟨Homo.zero⟩
  end

  section
    variable (G H : Abelian)

    instance : OfNat (Abelian.Hom G H) Nat.zero := ⟨@Homo.zero G.group H.group⟩
    instance : OfNat (Algebra.Hom G.1 H.1) Nat.zero := ⟨@Homo.zero G.group H.group⟩
  end

  noncomputable hott def Homo.set {G H : Group} : Structures.hset (Hom G H) :=
  Algebra.Hom.hset

  -- Of course, this can be done by induction
  hott def Homo.ofPath {G H : Group} (φ : G.carrier = H.carrier) (p : G.φ =[λ G, G → G → G, φ] H.φ) : Hom G H :=
  begin
    fapply mkhomo; exact @transport _ (λ G, G) G.carrier H.carrier φ;
    intros a b; transitivity; apply Id.map; apply bimap;
    iterate 2 { symmetry; apply @Equiv.transportForwardAndBack _ (λ G, G) _ _ φ };
    transitivity; symmetry; apply Equiv.transportOverOperationPointwise G.φ;
    apply HITs.Interval.happly; apply HITs.Interval.happly; exact p
  end

  hott def Iso.ofPath {G H : Group} (φ : G.carrier = H.carrier) (p : G.φ =[λ G, G → G → G, φ] H.φ) : G ≅ H :=
  begin
    fapply Iso.ofHom; apply Homo.ofPath φ p;
    apply Prod.mk <;> existsi @transport _ (λ G, G) H.carrier G.carrier (Id.inv φ) <;> intro x;
    dsimp; apply Equiv.transportForwardAndBack;
    apply @Equiv.transportBackAndForward _ (λ G, G) _ _ φ
  end

  noncomputable hott def Iso.ua {G H : Group} : (G ≅ H) → G = H :=
  begin intro φ; fapply Sigma.prod; apply Alg.ua φ; apply isGroupProp end

  -- This statement in fact says that two groups are equal
  -- if their multiplication tables are equal
  noncomputable hott def table {G H : Group} (φ : G.carrier = H.carrier)
    (p : G.φ =[λ G, G → G → G, φ] H.φ) : G = H :=
  Iso.ua (Iso.ofPath φ p)

  section
    variable {H : Group}
    hott def Op.mul := λ x y, H.φ y x
    hott def Op.inv := H.ι
    hott def Op.one := H.e
  end
end Group

namespace Group
  hott def Op (G : Group) : Group :=
  @Group.intro G.carrier G.hset Op.mul Op.inv Op.one
    (λ a b c, Id.inv (G.mulAssoc c b a))
    G.mulOne G.oneMul G.mulRightInv

  postfix:max "ᵒᵖ" => Op

  variable {G : Group}

  hott def Op.univ : Hom G Gᵒᵖ :=
  mkhomo G.ι invExplode

  hott def Op.iso : G ≅ Gᵒᵖ :=
  begin
    fapply mkiso; exact G.ι; apply invExplode;
    apply Prod.mk <;> existsi G.ι <;>
    intro <;> apply invInv
  end
end Group

namespace Group
  hott def Z₁.mul : 𝟏 → 𝟏 → 𝟏 := λ _ _, ★
  hott def Z₁.inv : 𝟏 → 𝟏     := λ _, ★

  instance Z₁.Mul : Mul 𝟏 := ⟨Z₁.mul⟩

  hott def Z₁ : Group :=
  @Group.intro 𝟏 unitIsSet Z₁.mul Z₁.inv ★ (λ _ _ _, idp _)
    (λ _, idp _) (λ _, idp _) (λ _, idp _)

  hott def Z₂.carrier := 𝟐

  hott def Z₂.mul : 𝟐 → 𝟐 → 𝟐
  | false => idfun
  | true  => not

  hott def Z₂.inv := @idfun Z₂.carrier

  hott def Z₂.set : Structures.hset Z₂.carrier :=
  Structures.Hedberg (λ | false, false => Sum.inl Id.refl
                        | true,  false => Sum.inr (ffNeqTt ∘ Id.inv)
                        | false, true  => Sum.inr ffNeqTt
                        | true,  true  => Sum.inl Id.refl)

  hott def Z₂ : Group :=
  @Group.intro Z₂.carrier Z₂.set Z₂.mul Z₂.inv false
    (begin
      intros a b c;
      induction a using Bool.casesOn <;>
      induction b using Bool.casesOn <;>
      induction c using Bool.casesOn <;>
      reflexivity
    end)
    (begin intro b; induction b using Bool.casesOn <;> reflexivity end)
    (begin intro b; induction b using Bool.casesOn <;> reflexivity end)
    (begin intro b; induction b using Bool.casesOn <;> reflexivity end)
end Group

end GroundZero.Algebra