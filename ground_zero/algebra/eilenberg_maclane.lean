import ground_zero.algebra.group ground_zero.theorems.prop
open ground_zero.theorems.functions ground_zero.theorems.prop
open ground_zero.types.equiv (idtoeqv)
open ground_zero.types.Id (dotted)
open ground_zero.ua (uaβrule)
open ground_zero.structures
open ground_zero.types
open ground_zero (ua)

namespace ground_zero.algebra
universes u v

hott theory

@[hott] noncomputable def ntype_is_succ_n_type (n : ℕ₋₂) :
  is-(hlevel.succ n)-type (n_type.{u} n) := begin
  intros x y,
  induction x with X p, induction y with Y p',
  apply ntype_respects_equiv,
  symmetry, apply sigma.sigma_path,
  { fapply ntype_respects_sigma,
    { apply ntype_respects_equiv,
      exact ground_zero.ua.univalence X Y,
      induction n with n ih,
      { existsi contr_type_equiv p p',
        intro e, fapply sigma.prod,
        { apply ground_zero.theorems.funext,
          intro x, apply contr_impl_prop, exact p' },
        { apply biinv_prop } },
      { fapply ntype_over_embedding, exact X → Y,
        apply prop_sigma_embedding,
        { intro x, apply biinv_prop },
        { apply pi_respects_ntype (hlevel.succ n),
          intro x, exact p' } } },
    { intros q, apply ground_zero.structures.prop_is_ntype,
      apply ntype_is_prop } }
end

@[hott] noncomputable def ens_is_groupoid : groupoid (0-Type) :=
begin apply one_eqv_groupoid.forward, apply ntype_is_succ_n_type 0 end

private structure K1.aux :=
(val : 𝟏)

def K1 (G : group) := K1.aux

namespace K1
  variables {G : group}
  local infix * := G.φ

  attribute [nothott] K1.aux.rec_on K1.aux.rec aux.val

  @[hott] def base : K1 G := ⟨★⟩

  axiom grpd     : groupoid (K1 G)
  axiom loop     : G.carrier → (base = base :> K1 G)
  axiom loop.mul : Π (x y : G.carrier), loop (x * y) = loop x ⬝ loop y

  @[safe] def ind {π : K1 G → Type v}
    (baseπ : π base) (loopπ : Π (x : G.carrier), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : G.carrier),
      loopπ (x * y) =[λ p, baseπ =[p] baseπ, loop.mul x y]
        loopπ x ⬝' loopπ y)
    (groupoidπ : Π x, groupoid (π x)) : Π x, π x
  | ⟨★⟩ := baseπ

  @[safe] def rec {π : Type v} (baseπ : π)
    (loopπ : G.carrier → baseπ = baseπ)
    (mulπ : Π x y, loopπ (x * y) = loopπ x ⬝ loopπ y)
    (groupoidπ : groupoid π) : K1 G → π
  | ⟨★⟩ := baseπ

  axiom indβrule {π : K1 G → Type v}
    (baseπ : π base) (loopπ : Π (x : G.carrier), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : G.carrier),
      loopπ (x * y) =[λ p, baseπ =[p] baseπ, loop.mul x y]
        loopπ x ⬝' loopπ y)
    (groupoidπ : Π x, groupoid (π x)) :
    Π x, equiv.apd (ind baseπ loopπ mulπ groupoidπ) (loop x) = loopπ x

  axiom recβrule {π : Type v} (baseπ : π) (loopπ : G.carrier → baseπ = baseπ)
    (mulπ : Π x y, loopπ (x * y) = loopπ x ⬝ loopπ y) (groupoidπ : groupoid π) :
    Π x, (rec baseπ loopπ mulπ @groupoidπ) # (loop x) = loopπ x

  attribute [irreducible] K1

  instance : dotted (K1 G) := ⟨base⟩

  def KΩ.mul : (Ω¹(K1 G)) → (Ω¹(K1 G)) → (Ω¹(K1 G)) := λ p q, p ⬝ q
  def KΩ.one :  Ω¹(K1 G)                            := idp base
  def KΩ.inv : (Ω¹(K1 G)) → (Ω¹(K1 G))              := Id.inv

  noncomputable def KΩ.magma (G : group) : magma :=
  ⟨@zeroeqv (Ω¹(K1 G)) (λ _ _, grpd), KΩ.mul⟩

  noncomputable def KΩ.semigroup (G : group) : semigroup :=
  ⟨KΩ.magma G, begin intros p q r, symmetry, apply Id.assoc end⟩

  noncomputable def KΩ.monoid (G : group) : monoid := begin
    fapply monoid.mk, exact KΩ.semigroup G, exact KΩ.one,
    intro p, apply Id.refl_left, apply Id.refl_right
  end

  noncomputable def KΩ (G : group) : group :=
  ⟨KΩ.monoid G, KΩ.inv, Id.inv_comp⟩

  noncomputable def homomorphism : G ⤳ KΩ G :=
  ⟨loop, loop.mul⟩

  noncomputable def loop.one : loop G.e = idp base :> Ω¹(K1 G) :=
  by apply group.homo_saves_unit homomorphism

  noncomputable def loop.inv (p : G.carrier) : loop (G.inv p) = (loop p)⁻¹ :=
  by apply group.homo_respects_inv homomorphism

  @[hott] noncomputable def family
    (baseπ : Type u)
    (loopπ : G.carrier → baseπ = baseπ)
    (mulπ : Π x y, loopπ (x * y) = loopπ x ⬝ loopπ y)
    (setπ : hset baseπ) : K1 G → (0-Type) :=
  begin
    fapply rec,
    { existsi baseπ, apply zero_eqv_set.left,
      intros p q, apply setπ },
    { intro x, fapply sigma.prod, apply loopπ x,
      apply ntype_is_prop },
    { intros x y, symmetry,
      transitivity, symmetry, apply sigma.prod_comp,
      fapply sigma.prod_eq, { symmetry, apply mulπ },
      { apply prop_is_set, apply ntype_is_prop } },
    { apply ens_is_groupoid }
  end

  @[hott] noncomputable def code' : K1 G → (0-Type) :=
  begin
    fapply family, exact G.carrier,
    { intro x, apply ground_zero.ua, existsi (* x), split;
      existsi (* G.inv x); intro y; change _ * _ * _ = _,
      repeat { transitivity, apply semigroup.mul_assoc,
               transitivity, apply Id.map },
      apply group.mul_right_inv, apply monoid.mul_one,
      apply group.mul_left_inv, apply monoid.mul_one },
    { intros x y, symmetry, transitivity,
      { symmetry, apply ground_zero.ua.ua_trans },
      apply Id.map ua, fapply sigma.prod,
      { apply ground_zero.theorems.funext, intro z,
        apply semigroup.mul_assoc },
      { apply biinv_prop } },
    { intros a b, apply G.set }
  end

  @[hott] def code (x : K1 G) := (code' x).fst

  @[hott] noncomputable def code.hset : Π (z : K1 G), hset (code z) :=
  begin
    intro z, fapply ind _ _ _ _ z,
    { intros a b, apply G.set },
    { intro x, change _ = _, apply set_is_prop },
    { intros x y, change _ = _, apply prop_is_set,
      apply set_is_prop },
    { intro x, apply one_eqv_groupoid.forward,
      apply prop_is_ntype _ 0, apply set_is_prop }
  end

  @[hott] noncomputable def hset_base : hset (@code G base) :=
  by intros p q; apply code.hset base

  @[hott] def encode : Π (z : K1 G), base = z → code z :=
  λ z p, equiv.transport code p G.e

  @[hott] noncomputable def decode : Π (z : K1 G), code z → base = z :=
  begin
    intro z, fapply ind _ _ _ _ z,
    { exact loop },
    { intro x, change _ = _, transitivity,
      apply @equiv.transport_characterization (K1 G) code (λ x, base = x),
      apply ground_zero.theorems.funext, intro y,
      transitivity, apply Id.map (λ p, equiv.transport (λ x, base = x) (loop x) (loop p)),
      transitivity, apply equiv.transport_to_transportconst,
      transitivity, apply Id.map (λ p, equiv.transportconst p y),
      transitivity, apply Id.map_inv, apply Id.map,
      transitivity, apply equiv.map_over_comp,
      transitivity, apply Id.map, apply recβrule,
      apply sigma.map_fst_over_prod,
      transitivity, apply equiv.transportconst_over_inv,
      apply ground_zero.ua.transportconst_inv_rule,
      transitivity, apply equiv.transport_over_inv_contr_map,
      transitivity, apply Id.map, apply equiv.idmap,
      transitivity, apply Id.map (⬝ loop x), apply loop.mul,
      transitivity, symmetry, apply Id.assoc,
      transitivity, apply Id.map, apply Id.map (⬝ loop x), apply loop.inv,
      transitivity, apply Id.map, apply Id.inv_comp, apply Id.refl_right },
    { intros x y,
      apply zero_eqv_set.forward,
      apply pi_respects_ntype 0,
      intro z, apply zero_eqv_set.left,
      apply grpd },
    { intro x, apply one_eqv_groupoid.forward,
      apply pi_respects_ntype 1,
      intro z, apply hlevel.cumulative 0,
      apply zero_eqv_set.left, apply grpd }
  end

  @[hott] noncomputable def encode_decode :
    Π (z : K1 G) (p : code z), encode z (decode z p) = p :=
  begin
    intros z p, fapply @ind G (λ z, Π (p : code z), encode z (decode z p) = p) _ _ _ _ z,
    { intro x, change G.carrier at x, change encode base (loop x) = _,
      transitivity, apply equiv.transport_to_transportconst,
      transitivity, apply Id.map (λ p, equiv.transportconst p G.e),
      transitivity, apply equiv.map_over_comp,
      transitivity, apply Id.map, apply recβrule,
      apply sigma.map_fst_over_prod,
      transitivity, apply ground_zero.ua.transportconst_rule,
      apply monoid.one_mul },
    { intros, apply ground_zero.theorems.funext, intro x,
      apply hset_base },
    { intros x y, apply prop_is_set,
      apply pi_prop, intro x, apply hset_base },
    { intro x, apply one_eqv_groupoid.forward,
      apply prop_is_ntype _ 0,
      intros p q, apply ground_zero.theorems.funext,
      intro y, apply code.hset x }
  end

  @[hott] noncomputable def decode_encode :
    Π (z : K1 G) (p : base = z), decode z (encode z p) = p :=
  begin intros z p, induction p, apply loop.one end

  @[hott] noncomputable def univ : G ≅ KΩ G := begin
    existsi loop, split,
    { intros x y, apply loop.mul },
    split; existsi encode base,
    { apply encode_decode base },
    { apply decode_encode base }
  end
end K1

end ground_zero.algebra