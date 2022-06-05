import GroundZero.Algebra.Group.Factor
open GroundZero.Algebra.Group (factorLeft)
open GroundZero.Types.Equiv (transport)
open GroundZero.Types.Id (map)
open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.Algebra
universe u v

namespace Prering
  inductive Arity : Type
  | nullary | unary | add | mul
  open Arity

  def signature : Arity + ⊥ → ℕ
  | Sum.inl nullary => 0
  | Sum.inl unary   => 1
  | Sum.inl add     => 2
  | Sum.inl mul     => 2
end Prering

def Prering : Type (u + 1) :=
Alg.{0, 0, u, 0} Prering.signature

namespace Overring
  def signature : Prering.Arity + 𝟏 → ℕ
  | Sum.inl v => Prering.signature (Sum.inl v)
  | Sum.inr _ => 2
end Overring

def Overring : Type (max u v + 1) :=
Alg.{0, 0, u, v} Overring.signature

namespace Prering
  hott def intro {α : Type u} (H : hset α)
    (φ ψ : α → α → α) (ι : α → α) (e : α) : Prering :=
  ⟨zeroeqv H,
    (λ | Arity.nullary => λ _, e
       | Arity.unary   => λ (a, _), ι a
       | Arity.add     => λ (a, b, _), φ a b
       | Arity.mul     => λ (a, b, _), ψ a b,
     λ z, nomatch z)⟩

  def zero (T : Prering) : T.carrier :=
  T.op Arity.nullary ★

  def neg (T : Prering) : T.carrier → T.carrier :=
  λ x, T.op Arity.unary (x, ★)

  def φ (T : Prering) : T.carrier → T.carrier → T.carrier :=
  λ x y, T.op Arity.add (x, y, ★)

  def ψ (T : Prering) : T.carrier → T.carrier → T.carrier :=
  λ x y, T.op Arity.mul (x, y, ★)

  hott def pregroup (T : Prering) : Pregroup :=
  Pregroup.intro T.hset T.φ T.neg T.zero

  abbrev additive := pregroup
end Prering

namespace Overring
  open Prering (Arity)

  hott def intro {α : Type u} (H : hset α) (φ ψ : α → α → α)
    (ι : α → α) (e : α) (ρ : α → α → Ω) : Overring :=
  ⟨zeroeqv H,
    (λ | Arity.nullary => λ _, e
       | Arity.unary   => λ (a, _), ι a
       | Arity.add     => λ (a, b, _), φ a b
       | Arity.mul     => λ (a, b, _), ψ a b,
     λ | ★             => λ (a, b, _), ρ a b)⟩

  def rel (T : Overring) (x y : T.carrier) : Ω := Alg.rel T ★ (x, y, ★)
  def ρ (T : Overring) (x y : T.carrier) := (T.rel x y).1

  def σ (T : Overring) (x y : T.carrier) := ¬(x = y) × T.ρ x y

  hott def τ (T : Overring) : Prering :=
  ⟨T.1, (T.2.1, λ z, nomatch z)⟩
end Overring

class ring (T : Prering) :=
(abgroup      : abelian T.pregroup)
(distribLeft  : Π a b c, T.ψ a (T.φ b c) = T.φ (T.ψ a b) (T.ψ a c))
(distribRight : Π a b c, T.ψ (T.φ a b) c = T.φ (T.ψ a c) (T.ψ b c))

postfix:max "⁺" => Prering.pregroup
instance abring (T : Prering) [ring T] : abelian T⁺ := ring.abgroup

section
  variable (T : Prering)
  def Prering.sub (x y : T.carrier) := T.φ x (T.neg y)

  def Prering.isproper (x : T.carrier) := T.pregroup.isproper x
  def Prering.proper := T.pregroup.proper

  def Prering.properHset : hset T.proper :=
  begin
    apply hsetRespectsSigma;
    apply T.pregroup.hset; intro;
    apply propIsSet; apply notIsProp
  end

  instance : Add T.carrier := ⟨T.φ⟩
  instance : Sub T.carrier := ⟨T.sub⟩
  instance : Neg T.carrier := ⟨T.neg⟩

  instance : Mul T.carrier := ⟨T.ψ⟩

  instance : OfNat T.carrier Nat.zero := ⟨T.zero⟩
end

section
  variable (T : Overring)

  instance : Add T.carrier := ⟨T.τ.φ⟩
  instance : Sub T.carrier := ⟨T.τ.sub⟩
  instance : Neg T.carrier := ⟨T.τ.neg⟩

  instance : Mul T.carrier := ⟨T.τ.ψ⟩

  instance : OfNat T.carrier Nat.zero := ⟨T.τ.zero⟩

  infix:70 " <= " => Overring.ρ _
  infix:70 " ≤ "  => Overring.ρ _
  infix:70 " >= " => λ x y, Overring.ρ _ y x
  infix:70 " ≥ "  => λ x y, Overring.ρ _ y x

  infix:70 " < " => Overring.σ _
  infix:70 " > " => λ x y, Overring.σ _ y x
end

namespace Prering
  variable (T : Prering) [ring T]

  hott def addAssoc (a b c : T.carrier) : (a + b) + c = a + (b + c) :=
  T.pregroup.mulAssoc a b c

  hott def zeroAdd (a : T.carrier) : 0 + a = a :=
  T.pregroup.oneMul a

  hott def addZero (a : T.carrier) : a + 0 = a :=
  T.pregroup.mulOne a

  hott def addComm (a b : T.carrier) : a + b = b + a :=
  T.pregroup.mulComm a b

  hott def addLeftNeg (a : T.carrier) : (-a) + a = 0 :=
  T.pregroup.mulLeftInv a

  hott def distribLeft (a b c : T.carrier) : a * (b + c) = a * b + a * c :=
  ring.distribLeft a b c

  hott def distribRight (a b c : T.carrier) : (a + b) * c = a * c + b * c :=
  ring.distribRight a b c
end Prering

section
  variable {T : Prering} [ring T]

  hott def ring.mulZero (a : T.carrier) : a * 0 = 0 :=
  begin
    apply @Group.unitOfSqr T⁺; transitivity;
    symmetry; apply ring.distribLeft;
    apply map (T.ψ a); apply T.zeroAdd
  end

  hott def ring.zeroMul (a : T.carrier) : 0 * a = 0 :=
  begin
    apply @Group.unitOfSqr T⁺; transitivity;
    symmetry; apply T.distribRight;
    apply map (· * a); apply T.addZero
  end

  hott def ring.mulNeg (a b : T.carrier) : a * (-b) = -(a * b) :=
  begin
    apply @Group.eqInvOfMulEqOne T⁺; transitivity;
    symmetry; apply T.distribLeft; transitivity;
    apply map (T.ψ a); apply T.addLeftNeg;
    apply ring.mulZero
  end

  hott def ring.negMul (a b : T.carrier) : (-a) * b = -(a * b) :=
  begin
    apply @Group.eqInvOfMulEqOne T⁺; transitivity;
    symmetry; apply T.distribRight; transitivity;
    apply map (· * b); apply T.addLeftNeg; apply ring.zeroMul
  end

  hott def ring.subDistribLeft (a b c : T.carrier) := calc
    a * (b - c) = a * b + a * (-c) : T.distribLeft a b (T.neg c)
            ... = a * b - a * c    : Id.map (T.φ (T.ψ a b)) (ring.mulNeg a c)

  hott def ring.subDistribRight (a b c : T.carrier) := calc
    (a - b) * c = a * c + (-b) * c : T.distribRight a (T.neg b) c
            ... = a * c - b * c    : Id.map (T.φ (T.ψ a c)) (ring.negMul b c)
end

class ring.assoc (T : Prering) :=
(mulAssoc : Π a b c, T.ψ (T.ψ a b) c = T.ψ a (T.ψ b c))

class ring.comm (T : Prering) :=
(mulComm : Π a b, T.ψ a b = T.ψ b a)

class ring.hasOne (T : Prering) :=
(one : T.carrier)

instance (T : Prering) [ring.hasOne T] : OfNat T.carrier (Nat.succ Nat.zero) := ⟨ring.hasOne.one⟩

class ring.monoid (T : Prering) extends ring.hasOne T :=
(oneMul : Π a, T.ψ 1 a = a)
(mulOne : Π a, T.ψ a 1 = a)

class ring.hasInv (T : Prering) :=
(inv : T.carrier → T.carrier)

postfix:max (priority := high) "⁻¹" => ring.hasInv.inv

class ring.divisible (T : Prering) extends ring.hasInv T, ring.monoid T :=
(zero_inv   : inv 0 = 0)
(mulLeftInv : Π (x : T.carrier), T.isproper x → inv x * x = 1)

class field (T : Prering) extends ring T, ring.assoc T, ring.divisible T, ring.comm T :=
(nontrivial : T.isproper 1)

hott def ring.minusOneSqr (T : Prering) [ring T] [ring.monoid T] : @Id T.carrier ((-1) * (-1)) 1 :=
begin
  transitivity; apply ring.mulNeg;
  transitivity; apply Id.map T.neg;
  apply ring.monoid.mulOne;
  apply @Group.invInv T⁺
end

hott def field.properMul {T : Prering} [field T] {a b : T.carrier} :
  T.isproper a → T.isproper b → T.isproper (a * b) :=
begin
  intros p q r; apply @field.nontrivial T _;
  transitivity; { symmetry; apply ring.divisible.mulLeftInv b q };
  transitivity; { apply map (· * b); symmetry; apply ring.monoid.mulOne };
  transitivity; apply ring.assoc.mulAssoc;
  transitivity; apply map (λ y, b⁻¹ * (y * b));
  { symmetry; apply ring.divisible.mulLeftInv a p };
  transitivity; apply map (T.ψ _); apply ring.assoc.mulAssoc;
  transitivity; { symmetry; apply ring.assoc.mulAssoc };
  transitivity; apply map; exact r; apply ring.mulZero
end

hott def field.propInv {T : Prering} [field T] {a : T.carrier} : T.isproper a → T.isproper a⁻¹ :=
begin
  intros p q; apply @field.nontrivial T _;
  transitivity; { symmetry; apply ring.divisible.mulLeftInv a p };
  transitivity; apply map (· * a); exact q; apply ring.zeroMul
end

hott def field.mul (T : Prering) [field T] :
  T.proper → T.proper → T.proper :=
λ ⟨a, p⟩ ⟨b, q⟩, ⟨T.ψ a b, field.properMul p q⟩

hott def field.rev (T : Prering) [field T] : T.proper → T.proper :=
λ ⟨a, p⟩, ⟨a⁻¹, field.propInv p⟩

hott def ring.properEq {T : Prering.{u}}
  {x y : T.proper} (p : x.fst = y.fst) : x = y :=
begin fapply Sigma.prod; exact p; apply notIsProp end

hott def multiplicative (T : Prering) [field T] : Pregroup :=
Pregroup.intro T.properHset (field.mul T) (field.rev T) ⟨ring.hasOne.one, field.nontrivial⟩
postfix:max "ˣ" => multiplicative

section
  variable (T : Prering) [field T]

  instance multiplicative.semigroup : semigroup Tˣ.magma :=
  ⟨λ ⟨a, p⟩ ⟨b, q⟩ ⟨c, r⟩, begin
    fapply @ring.properEq T;
    apply @ring.assoc.mulAssoc T
  end⟩

  instance multiplicative.monoid : monoid Tˣ.premonoid :=
  ⟨multiplicative.semigroup T,
  λ ⟨a, p⟩, ring.properEq (ring.monoid.oneMul a),
  λ ⟨a, p⟩, ring.properEq (ring.monoid.mulOne a)⟩

  instance multiplicative.group : group Tˣ :=
  ⟨multiplicative.monoid T, λ ⟨a, p⟩, ring.properEq (ring.divisible.mulLeftInv a p)⟩
end

-- voilà, no need to repeat a bunch of lemmas
hott def field.mulRightInv (T : Prering) [field T] {x : T.carrier}
  (p : T.isproper x) : x * x⁻¹ = 1 :=
Id.map Sigma.fst (@Group.mulRightInv Tˣ _ ⟨x, p⟩)

class lid (T : Prering) (φ : T⁺.subgroup) :=
(ideal : Π r i, i ∈ φ.set → T.ψ r i ∈ φ.set)

class rid (T : Prering) (φ : T⁺.subgroup) :=
(ideal : Π i r, i ∈ φ.set → T.ψ i r ∈ φ.set)

class ideal (T : Prering) (φ : T⁺.subgroup) :=
(left  : Π r i, i ∈ φ.set → T.ψ r i ∈ φ.set)
(right : Π i r, i ∈ φ.set → T.ψ i r ∈ φ.set)

instance ideal.auto (T : Prering) (φ : T⁺.subgroup)
  [lid T φ] [rid T φ] : ideal T φ :=
⟨lid.ideal, rid.ideal⟩

namespace Ring
  variable (T : Prering) [ring T] (φ : T⁺.subgroup) [ideal T φ]

  instance normal : T⁺ ⊵ φ :=
  Group.abelianSubgroupIsNormal T⁺ φ

  noncomputable def Factor.mul : factorLeft T⁺ φ → factorLeft T⁺ φ → factorLeft T⁺ φ :=
  begin
    fapply HITs.Quotient.lift₂;
    { intros a b; apply HITs.Quotient.elem; exact T.ψ a b };
    { apply HITs.Quotient.set };
    { intros a₁ a₂ b₁ b₂ p q; apply HITs.Quotient.sound; apply transport (· ∈ φ.set);
      { let φ' := @Pregroup.leftDiv T⁺;
        change T.φ (φ' (T.ψ a₁ a₂) (T.ψ a₁ b₂)) (φ' (T.ψ a₁ b₂) (T.ψ b₁ b₂)) = _;
        transitivity; apply T⁺.mulAssoc;
        transitivity; apply Id.map (T.φ _);
        transitivity; symmetry; apply T⁺.mulAssoc;
        apply Id.map (λ z, T.φ z (T.ψ b₁ b₂));
        apply Group.mulRightInv; apply Id.map; apply T.zeroAdd };
      apply φ.mul;
      { apply transport (· ∈ φ.set);
        transitivity; apply T.distribLeft a₁ (T.neg a₂) b₂;
        apply Id.map (λ z, T.φ z (T.ψ a₁ b₂));
        apply ring.mulNeg; apply ideal.left; exact q };
      { apply transport (· ∈ φ.set);
        transitivity; apply T.distribRight (T.neg a₁) b₁ b₂;
        apply Id.map (λ z, T.φ z (T.ψ b₁ b₂));
        apply ring.negMul; apply ideal.right; exact p } }
  end

  noncomputable hott def Factor : Prering :=
  Prering.intro (T⁺\φ).hset (T⁺\φ).φ (Factor.mul T φ) (T⁺\φ).ι (T⁺\φ).e

  noncomputable instance Factor.abgroup : abelian (T⁺\φ) :=
  ⟨begin
    intro (x : HITs.Quotient _) (y : HITs.Quotient _); induction x; induction y;
    apply Id.map HITs.Quotient.elem; apply T.addComm;
    apply HITs.Quotient.set; apply propIsSet; apply HITs.Quotient.set;
    apply HITs.Quotient.set; apply propIsSet; apply HITs.Quotient.set
  end⟩

  -- how??
  -- (deterministic) timeout at 'elaborator', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

  /-
  noncomputable instance Factor.ring : ring (Factor T φ) :=
  ⟨Factor.abgroup T φ, begin
    fapply HITs.Quotient.indProp;
  end, begin
    skip
  end⟩
  -/

  infix:80 " \\ " => Factor
end Ring
end GroundZero.Algebra
