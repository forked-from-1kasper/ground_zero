import ground_zero.algebra.group.isomorphism ground_zero.algebra.group.free
open ground_zero.types.equiv (biinv transport)
open ground_zero.types.Id (map)
open ground_zero.structures
open ground_zero.types
open ground_zero.proto
open ground_zero

/-
  Group presentation, presentation of every group.
  * https://en.wikipedia.org/wiki/Presentation_of_a_group#Definition

  Abelianization (as factor group).
  * https://groupprops.subwiki.org/wiki/Abelianization
  * https://ncatlab.org/nlab/show/abelianization

  Free abelian group.
  * https://en.wikipedia.org/wiki/Free_abelian_group
-/

namespace ground_zero.algebra
universes u v u' v' w

hott theory

namespace group
  variables {G : pregroup} [group G]
  local infix ` * `  := G.φ
  local notation `e` := G.e
  local postfix ⁻¹   := G.ι

  @[hott] def closure.set (G : pregroup) (x : G.subset) : G.subset :=
  ens.smallest (λ φ, pregroup.is_subgroup G φ × normal G φ × x ⊆ φ)

  @[hott] def closure.sub (φ : G.subset) : φ ⊆ closure.set G φ :=
  begin intros x G y H, apply H.snd.snd, assumption end

  @[hott] def closure.sub_trans {φ : G.subset} {ψ : G.subgroup} [p : G ⊵ ψ] :
    φ ⊆ ψ.set → closure.set G φ ⊆ ψ.set :=
  begin
    intros H x G, apply G, split, exact ψ.snd,
    split, exact p.cosets_eqv, exact H
  end

  @[hott] def closure.elim (φ : G.subgroup) [G ⊵ φ] :
    closure.set G φ.set ⊆ φ.set :=
  closure.sub_trans (ens.ssubset.refl φ.set)

  @[hott] def closure (x : G.subset) : G.subgroup :=
  begin
    fapply pregroup.subgroup.mk,
    exact closure.set G x,
    { intros y H, induction H with G H, apply G.fst },
    { intros a b G H y F, apply F.fst.snd.fst,
      apply G y, assumption, apply H y, assumption },
    { intros a H y G, apply G.fst.snd.snd,
      apply H y, assumption }
  end

  @[hott] instance closure.normal_subgroup (x : G.subset) : G ⊵ closure x :=
  begin split, intros g h G y H, apply H.snd.fst, apply G y, assumption end

  section
    variables {ε : Type u} (R : (F ε).subset)
    @[hott] noncomputable def presentation :=
    (F ε)\(closure R)

    @[hott] def presentation.carrier :=
    factor_left (F ε) (closure R)

    @[hott] noncomputable def presentation.one : presentation.carrier R :=
    (presentation R).e
  end

  @[hott] noncomputable def presentation.sound {α : Type u}
    {R : (F α).subset} {x : F.carrier α} (H : x ∈ R) :
      factor.incl x = presentation.one R :> (presentation R).carrier :=
  begin apply factor.sound, apply closure.sub, assumption end

  @[hott] def commutators (G : pregroup) [group G] : G.subset :=
  ground_zero.algebra.im (function.uncurry commutator)

  @[hott] noncomputable def abelianization (G : pregroup) [group G] :=
  G\closure (commutators G)
  postfix `ᵃᵇ`:2000 := abelianization

  @[hott] def abelianization.elem : G.carrier → (abelianization G).carrier :=
  factor.incl

  @[hott] noncomputable instance abelianization.group :
    group (abelianization G) :=
  by apply factor.group

  @[hott] noncomputable instance abelianization.abelian :
    abelian (abelianization G) :=
  begin
    split, intros a b, apply @commutes (abelianization G),
    fapply HITs.quot.ind _ _ _ a; clear a; intro a,
    { fapply HITs.quot.ind _ _ _ b; clear b; intro b,
      { apply factor.sound, intros y H,
        apply H.snd.snd, apply HITs.merely.elem,
        existsi (a, b), trivial },
      { intros, apply HITs.quot.set },
      { apply prop_is_set, apply HITs.quot.set } },
    { intros, apply HITs.quot.set },
    { apply prop_is_set, apply HITs.quot.set }
  end

  section
    variables {H : pregroup} [abelian H]
    local infix ×:70 := H.φ

    @[hott] def commutators.to_ker (f : G ⤳ H) : commutators G ⊆ (ker f).set :=
    begin
      intros x, fapply HITs.merely.rec,
      { apply ens.prop },
      { intro H, induction H with p q, induction f with f F,
        induction p with a b, change _ = _, calc
          f x = f (a * b * (a⁻¹ * b⁻¹))     : f # (Id.inv q)
          ... = f (a * b) × f (a⁻¹ * b⁻¹)   : homo_mul ⟨f, F⟩ (a * b) (a⁻¹ * b⁻¹)
          ... = f (a * b) × (f a⁻¹ × f b⁻¹) : by apply Id.map; apply homo_mul ⟨f, F⟩
          ... = f (a * b) × (f b⁻¹ × f a⁻¹) : by apply Id.map; apply abelian.mul_comm
          ... = f (a * b) × f (b⁻¹ * a⁻¹)   : by apply Id.map; symmetry; apply homo_mul ⟨f, F⟩
          ... = f (a * b * (b⁻¹ * a⁻¹))     : Id.inv (homo_mul ⟨f, F⟩ _ _)
          ... = f (a * b * b⁻¹ * a⁻¹)       : f # (Id.inv (G.mul_assoc _ _ _))
          ... = f (a * (b * b⁻¹) * a⁻¹)     : @Id.map G.carrier H.carrier _ _
                                                (λ x, f (x * a⁻¹))
                                                (G.mul_assoc a b b⁻¹)
          ... = f (a * e * a⁻¹)             : @Id.map G.carrier H.carrier _ _
                                                (λ x, f (a * x * a⁻¹))
                                                (mul_right_inv b)
          ... = f (a * a⁻¹)                 : @Id.map G.carrier H.carrier _ _
                                                (λ x, f (x * a⁻¹)) (G.mul_one a)
          ... = f e                         : f # (mul_right_inv a)
          ... = H.e                         : homo_unit ⟨f, F⟩ }
    end
  end

  @[hott] def commutators.to_closure_ker {H : pregroup} [abelian H] (f : G ⤳ H) :
    ens.ssubset (closure.set G (commutators G)) (ker f).set :=
  closure.sub_trans (commutators.to_ker f)

  @[hott] def abelianization.rec {ε α : pregroup} [group ε] [abelian α] (f : ε ⤳ α) :
    εᵃᵇ.carrier → α.carrier :=
  begin
    fapply factor.lift, exact f,
    { intros x H, apply commutators.to_closure_ker, assumption }
  end

  @[hott] noncomputable def abelianization.homomorphism {ε α : pregroup}
    [group ε] [abelian α] (f : ε ⤳ α) : εᵃᵇ ⤳ α :=
  mkhomo (abelianization.rec f) (begin
    intros a b, fapply HITs.quotient.ind_prop _ _ a; clear a; intro a,
    { fapply HITs.quotient.ind_prop _ _ b; clear b; intro b,
      { apply homo_mul }, { apply α.hset } },
    { apply α.hset }
  end)

  @[hott] noncomputable def FAb (α : Type u) := abelianization (F α)
  @[hott] noncomputable instance {α : Type u} : abelian (FAb α) :=
  by apply abelianization.abelian

  @[hott] noncomputable def FAb.elem {α : Type u} : α → (FAb α).carrier :=
  abelianization.elem ∘ F.elem

  @[hott] noncomputable def FAb.rec {α : pregroup} [abelian α] {ε : Type v}
    (f : ε → α.carrier) : (FAb ε).carrier → α.carrier :=
  abelianization.rec (F.homomorphism f)

  @[hott] noncomputable def FAb.homomorphism {α : pregroup} [abelian α] {ε : Type v}
    (f : ε → α.carrier) : FAb ε ⤳ α :=
  abelianization.homomorphism (F.homomorphism f)

  @[hott] noncomputable def normal_factor (φ : G.subgroup) [G ⊵ φ] :
    G\φ ≅ G\closure φ.set :=
  factor.iso (closure.sub φ.set) (closure.elim φ)

  @[hott] noncomputable def F.homomorphism.encode :
    G.carrier → im.carrier (F.homomorphism id) :=
  λ x, ⟨x, HITs.merely.elem ⟨F.elem x, idp _⟩⟩

  @[hott] noncomputable def F.homomorphism.iso :
    G ≅ Im (F.homomorphism (@id G.carrier)) :=
  begin
    fapply mkiso, exact F.homomorphism.encode,
    { intros x y, fapply sigma.prod,
      { reflexivity },
      { apply HITs.merely.uniq } },
    { split; existsi sigma.fst,
      { intro x, trivial },
      { intro x, induction x with x H,
        fapply sigma.prod,
        { reflexivity },
        { apply HITs.merely.uniq } } }
  end

  @[hott] noncomputable def presentation.univ :
    Σ (R : (F G.carrier).subset), G ≅ presentation R :=
  begin
    existsi (ker (F.homomorphism id)).set,
    apply iso.trans F.homomorphism.iso,
    apply iso.trans first_iso_theorem,
    apply normal_factor
  end
end group

end ground_zero.algebra