import GroundZero.Algebra.Group.Isomorphism
import GroundZero.Algebra.Group.Free

open GroundZero.Types.Equiv (biinv transport)
open GroundZero.Types.Id (map)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero

/-
  Group presentation, presentation of every group.
  * https://en.wikipedia.org/wiki/presentation_of_a_group#Definition

  Abelianization (as factor group).
  * https://groupprops.subwiki.org/wiki/abelianization
  * https://ncatlab.org/nlab/show/abelianization

  Free abelian group.
  * https://en.wikipedia.org/wiki/Free_abelian_group
-/

namespace GroundZero.Algebra

namespace Group
  variable {G : Group}

  universe u v

  hott def Closure.set (G : Group.{u}) (x : Group.subset.{u, v} G) : G.subset :=
  Ens.smallest.{u, v, max u v} (λ φ, G.isSubgroup φ × G.isNormal φ × x ⊆ φ)

  hott def Closure.sub (φ : G.subset) : φ ⊆ Closure.set G φ :=
  begin intros x G y H; apply H.2.2; assumption end

  hott def Closure.subTrans {φ : G.subset} {ψ : G.normal} : φ ⊆ ψ.set → Closure.set G φ ⊆ ψ.set :=
  begin
    intros H x G; apply G; apply Prod.mk;
    exact ψ.1.2; apply Prod.mk; exact ψ.2; exact H
  end

  hott def Closure.elim (φ : G.normal) :
    Closure.set G φ.set ⊆ φ.set :=
  Closure.subTrans (Ens.ssubset.refl φ.set)

  hott def Closure (x : G.subset) : G.normal :=
  ⟨begin
    fapply Group.subgroup.mk; exact Closure.set G x;
    { intro y ⟨G, H⟩; apply G.1 };
    { intro a b G H y F; apply F.1.2.1;
      apply G y; assumption; apply H y; assumption };
    { intro a H y G; apply G.1.2.2; apply H y; assumption }
  end,
  begin intros g h G y H; apply H.2.1; apply G y; assumption end⟩

  section
    variable {ε : Type u} (R : (F ε).subset)
    noncomputable hott def Presentation :=
    (F ε)\(Closure R)

    hott def Presentation.carrier :=
    factorLeft (F ε) (Closure R)

    noncomputable hott def Presentation.one : Presentation.carrier R :=
    (Presentation R).e
  end

  noncomputable hott def Presentation.sound {A : Type u}
    {R : (F A).subset} {x : F.carrier A} (H : x ∈ R) :
      Factor.incl x = Presentation.one R :=
  begin apply Factor.sound; apply Closure.sub; assumption end

  hott def commutators (G : Group) : G.subset :=
  GroundZero.Algebra.im (λ (a, b), commutator a b)

  noncomputable hott def Abelianization (G : Group) :=
  G\Closure (commutators G)
  postfix:max "ᵃᵇ" => Abelianization

  hott def Abelianization.elem : G.carrier → (Abelianization G).carrier :=
  Factor.incl

  noncomputable def abelComm : (Abelianization G).isCommutative :=
  begin
    intro (a : HITs.Quotient _) (b : HITs.Quotient _);
    apply @commutes (Abelianization G); induction a; case elemπ a =>
    { induction b; case elemπ b =>
      { apply Factor.sound; intros y H; apply H.2.2; apply HITs.Merely.elem;
        existsi (a, b); reflexivity };
      apply HITs.Quotient.set; apply propIsSet; apply HITs.Quotient.set };
      apply HITs.Quotient.set; apply propIsSet; apply HITs.Quotient.set
  end

  section
    variable {H : Group} (ρ : H.isCommutative)

    hott def commutators.toKer (f : Hom G H) : commutators G ⊆ (ker f).set :=
    begin
      intro x; fapply HITs.Merely.rec; apply Ens.prop;
      intro ⟨(a, b), q⟩; change _ = _; apply calc
        f.1 x = f.1 (G.φ (G.φ a b) (G.φ (G.ι a) (G.ι b)))             : Id.map f.1 (Id.inv q)
          ... = H.φ (f.1 (G.φ a b)) (f.1 (G.φ (G.ι a) (G.ι b)))       : homoMul f _ _
          ... = H.φ (f.1 (G.φ a b)) (H.φ (f.1 (G.ι a)) (f.1 (G.ι b))) : Id.map _ (homoMul f _ _)
          ... = H.φ (f.1 (G.φ a b)) (H.φ (f.1 (G.ι b)) (f.1 (G.ι a))) : Id.map _ (ρ _ _)
          ... = H.φ (f.1 (G.φ a b)) (f.1 (G.φ (G.ι b) (G.ι a)))       : Id.map _ (homoMul f _ _)⁻¹
          ... = f.1 (G.φ (G.φ a b) (G.φ (G.ι b) (G.ι a)))             : Id.inv (homoMul f _ _)
          ... = f.1 (G.φ (G.φ (G.φ a b) (G.ι b)) (G.ι a))             : Id.map f.1 (Id.inv (G.mulAssoc _ _ _))
          ... = f.1 (G.φ (G.φ a (G.φ b (G.ι b))) (G.ι a))             : @Id.map G.carrier H.carrier _ _ (λ x, f.1 (G.φ x (G.ι a))) (G.mulAssoc a b (G.ι b))
          ... = f.1 (G.φ (G.φ a G.e) (G.ι a))                         : @Id.map G.carrier H.carrier _ _ (λ x, f.1 (G.φ (G.φ a x) (G.ι a))) (mulRightInv b)
          ... = f.1 (G.φ a (G.ι a))                                   : @Id.map G.carrier H.carrier _ _ (λ x, f.1 (G.φ x (G.ι a))) (G.mulOne a)
          ... = f.1 G.e                                               : Id.map f.1 (mulRightInv a)
          ... = H.e                                                   : homoUnit f
    end
  end

  hott def commutators.toClosureKer {H : Group} (ρ : H.isCommutative) (f : Hom G H) :
    Ens.ssubset (Closure.set G (commutators G)) (ker f).set :=
  Closure.subTrans (commutators.toKer ρ f)

  hott def Abelianization.rec {G A : Group} (ρ : A.isCommutative)
    (f : Hom G A) : Gᵃᵇ.carrier → A.carrier :=
  begin
    fapply Factor.lift; exact f; intros x H;
    apply commutators.toClosureKer ρ; assumption
  end

  noncomputable hott def Abelianization.homomorphism {G A : Group} (ρ : A.isCommutative) (f : Hom G A) : Hom Gᵃᵇ A :=
  mkhomo (Abelianization.rec ρ f) (begin
    intro (a : HITs.Quotient _) (b : HITs.Quotient _);
    induction a; induction b; apply homoMul;
    apply A.hset; apply propIsSet; apply A.hset;
    apply A.hset; apply propIsSet; apply A.hset
  end)

  noncomputable hott def FAb (A : Type u) := Abelianization (F A)

  noncomputable hott def FAb.elem {A : Type u} : A → (FAb A).carrier :=
  Abelianization.elem ∘ F.elem

  noncomputable hott def FAb.rec {A : Group} (ρ : A.isCommutative)
    {ε : Type v} (f : ε → A.carrier) : (FAb ε).carrier → A.carrier :=
  Abelianization.rec ρ (F.homomorphism f)

  noncomputable hott def FAb.homomorphism {A : Group} (ρ : A.isCommutative)
    {ε : Type v} (f : ε → A.carrier) : Hom (FAb ε) A :=
  Abelianization.homomorphism ρ (F.homomorphism f)

  noncomputable hott def normalFactor (φ : G.normal) : G\φ ≅ G\Closure φ.set :=
  Factor.iso (Closure.sub φ.set) (Closure.elim φ)

  noncomputable hott def F.homomorphism.encode :
    G.carrier → im.carrier (@F.homomorphism G G.carrier id) :=
  λ x, ⟨x, HITs.Merely.elem ⟨F.elem x, idp _⟩⟩

  noncomputable hott def F.homomorphism.iso :
    G ≅ Im (@F.homomorphism G G.carrier id) :=
  begin
    fapply mkiso; exact F.homomorphism.encode;
    { intros x y; fapply Sigma.prod;
      reflexivity; apply HITs.Merely.uniq };
    { apply Prod.mk <;> existsi Sigma.fst;
      { intro; reflexivity };
      { intro; fapply Sigma.prod;
        reflexivity; apply HITs.Merely.uniq } }
  end

  noncomputable hott def Presentation.univ :
    Σ (R : (F G.carrier).subset), G ≅ Presentation R :=
  begin
    existsi (ker (F.homomorphism id)).set;
    apply Iso.trans F.homomorphism.iso;
    apply Iso.trans firstIsoTheorem;
    apply normalFactor
  end
end Group

end GroundZero.Algebra