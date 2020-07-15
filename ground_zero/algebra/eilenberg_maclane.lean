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
      { fapply ntype_over_embedding equiv.forward,
        { apply prop_sigma_embedding, apply biinv_prop },
        { apply pi_respects_ntype (hlevel.succ n),
          intro x, apply p' } } },
    { intros q, apply ground_zero.structures.prop_is_ntype,
      apply ntype_is_prop } }
end

@[hott] noncomputable def ens_is_groupoid : groupoid (0-Type) :=
begin apply one_eqv_groupoid.forward, apply ntype_is_succ_n_type 0 end

private structure K1.aux :=
(val : 𝟏)

def K1 (α : Type u) [group α] := K1.aux

namespace K1
  variables {α : Type u} [group α]

  attribute [nothott] K1.aux.rec_on K1.aux.rec aux.val

  @[hott] def base : K1 α := ⟨★⟩

  axiom grpd     : groupoid (K1 α)
  axiom loop     : α → (base = base :> K1 α)
  axiom loop.mul : Π (x y : α), loop (x * y) = loop x ⬝ loop y

  @[safe] def ind {π : K1 α → Type v}
    (baseπ : π base) (loopπ : Π (x : α), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : α),
      loopπ (x * y) =[λ p, baseπ =[p] baseπ, loop.mul x y]
        loopπ x ⬝' loopπ y)
    (groupoidπ : Π x, groupoid (π x)) : Π x, π x
  | ⟨★⟩ := baseπ

  @[safe] def rec {π : Type v} (baseπ : π)
    (loopπ : α → baseπ = baseπ)
    (mulπ : Π x y, loopπ (x * y) = loopπ x ⬝ loopπ y)
    (groupoidπ : groupoid π) : K1 α → π
  | ⟨★⟩ := baseπ

  axiom indβrule {π : K1 α → Type v}
    (baseπ : π base) (loopπ : Π (x : α), baseπ =[loop x] baseπ)
    (mulπ : Π (x y : α),
      loopπ (x * y) =[λ p, baseπ =[p] baseπ, loop.mul x y]
        loopπ x ⬝' loopπ y)
    (groupoidπ : Π x, groupoid (π x)) :
    Π x, equiv.apd (ind baseπ loopπ mulπ groupoidπ) (loop x) = loopπ x

  axiom recβrule {π : Type v} (baseπ : π) (loopπ : α → baseπ = baseπ)
    (mulπ : Π x y, loopπ (x * y) = loopπ x ⬝ loopπ y) (groupoidπ : groupoid π) :
    Π x, (rec baseπ loopπ mulπ @groupoidπ) # (loop x) = loopπ x

  attribute [irreducible] K1

  instance : dotted (K1 α) := ⟨base⟩

  instance : has_mul (Ω¹(K1 α)) := ⟨λ p q, p ⬝ q⟩
  instance : has_one (Ω¹(K1 α)) := ⟨idp base⟩
  instance : has_inv (Ω¹(K1 α)) := ⟨Id.inv⟩

  noncomputable instance : magma (Ω¹(K1 α)) :=
  begin split, apply grpd end

  noncomputable instance : semigroup (Ω¹(K1 α)) :=
  begin split, intros p q r, symmetry, apply Id.assoc end

  noncomputable instance : monoid (Ω¹(K1 α)) := begin
    split; intro p, apply Id.refl_left, apply Id.refl_right
  end

  noncomputable instance : group (Ω¹(K1 α)) :=
  begin split, intro p, apply Id.inv_comp end

  noncomputable def homomorphism : α ⤳ Ω¹(K1 α) :=
  ⟨loop, loop.mul⟩

  noncomputable def loop.one : loop 1 = idp base :> Ω¹(K1 α) :=
  by apply group.homo_saves_unit homomorphism

  noncomputable def loop.inv (p : α) : loop p⁻¹ = (loop p)⁻¹ :=
  by apply group.homo_respects_inv homomorphism

  @[hott] noncomputable def family
    (baseπ : Type u)
    (loopπ : α → baseπ = baseπ)
    (mulπ : Π x y, loopπ (x * y) = loopπ x ⬝ loopπ y)
    (setπ : hset baseπ) : K1 α → (0-Type) := begin
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

  @[hott] noncomputable def code' : K1 α → (0-Type) := begin
    fapply family, exact α,
    { intro x, apply ground_zero.ua, existsi (* x), split;
      existsi (* x⁻¹); intro y; change _ * _ * _ = _,
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
    { apply magma.set }
  end

  @[hott] def code : K1 α → Type u := sigma.fst ∘ code'

  @[hott] noncomputable def code.hset : Π (z : K1 α), hset (code z) := begin
    intro z, fapply ind _ _ _ _ z,
    { change hset α, apply magma.set },
    { intro x, change _ = _, apply set_is_prop },
    { intros x y, change _ = _, apply prop_is_set,
      apply set_is_prop },
    { intro x, apply one_eqv_groupoid.forward,
      apply prop_is_ntype _ 0, apply set_is_prop }
  end

  @[hott] noncomputable def hset_base : hset (@code α _ base) :=
  by intros p q; apply code.hset base

  @[hott] def encode : Π (z : K1 α), base = z → code z :=
  λ z p, equiv.transport code p (1 : α)

  @[hott] noncomputable def decode : Π (z : K1 α), code z → base = z := begin
    intro z, fapply ind _ _ _ _ z,
    { exact loop },
    { intro x, change _ = _, transitivity,
      apply @equiv.transport_characterization (K1 α) code (λ x, base = x),
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
    Π (z : K1 α) (p : code z), encode z (decode z p) = p := begin
    intros z p, fapply @ind α _ (λ z,
      Π (p : code z), encode z (decode z p) = p) _ _ _ _ z,
    { intro x, change α at x, change encode base (loop x) = _,
      transitivity, apply equiv.transport_to_transportconst,
      transitivity, apply Id.map (λ p, equiv.transportconst p (1 : α)),
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
    Π (z : K1 α) (p : base = z), decode z (encode z p) = p :=
  begin intros z p, induction p, apply loop.one end

  @[hott] noncomputable def univ : α ≅ Ω¹(K1 α) := begin
    existsi loop, split,
    { intros x y, apply loop.mul },
    split; existsi encode base,
    { apply encode_decode base },
    { apply decode_encode base }
  end
end K1

end ground_zero.algebra