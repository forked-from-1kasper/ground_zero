import GroundZero.Modal.Infinitesimal
import GroundZero.Structures

open GroundZero.Types GroundZero.Proto
open GroundZero.Types.Equiv
open GroundZero

namespace GroundZero.HITs.Infinitesimal
universe u v w

-- infinitesimally close
hott def infinitesimallyClose {A : Type u} (a b : A) := ι a = ι b
infix:80 " ~ " => infinitesimallyClose

hott def Disc {A : Type u} (a : A) := Σ b, a ~ b
notation "𝔻" => Disc

hott def discBundle (A : Type u) := Σ (a : A), 𝔻 a
notation "T∞" => discBundle

hott def center {A : Type u} (a : A) : 𝔻 a := ⟨a, idp (ι a)⟩

noncomputable section
  variable {A : Type u} {B : Type v} (f : A → B)

  hott def infProxAp {a b : A} : a ~ b → f a ~ f b :=
  λ ρ, (Im.naturality f a)⁻¹ ⬝ Id.ap (Im.ap f) ρ ⬝ Im.naturality f b

  hott def d (x : A) : 𝔻 x → 𝔻 (f x) :=
  λ ε, ⟨f ε.1, infProxAp f ε.2⟩

  hott def bundleAp : T∞ A → T∞ B :=
  λ τ, ⟨f τ.1, d f τ.1 τ.2⟩
end

hott def infProxApIdp {A : Type u} {a b : A} (ρ : a ~ b) : infProxAp idfun ρ = ρ :=
begin
  symmetry; transitivity; symmetry; apply Equiv.idmap;
  transitivity; apply mapWithHomotopy _ _ Im.apIdfun;
  apply bimap (· ⬝ _ ⬝ ·); apply Im.indεβrule;
  transitivity; apply Id.ap; apply Im.indεβrule; apply Id.invInv
end

hott def infProxApCom {A : Type u} {B : Type v} {C : Type w} (f : B → C) (g : A → B)
  {a b : A} (ρ : a ~ b) : infProxAp (f ∘ g) ρ = infProxAp f (infProxAp g ρ) :=
begin
  transitivity; apply Id.ap (_ ⬝ · ⬝ _);
  transitivity; apply mapWithHomotopy _ _ (Im.apCom _ _);
  apply bimap; apply bimap; apply Im.indεβrule;
  apply mapOverComp; apply Id.ap; apply Im.indεβrule;

  transitivity; apply Id.ap (· ⬝ _); apply Id.assoc;
  transitivity; apply Id.ap (· ⬝ _ ⬝ _); apply Id.assoc;
  transitivity; symmetry; apply Id.assoc;

  symmetry; transitivity; apply Id.ap (_ ⬝ · ⬝ _); transitivity;
  apply mapFunctoriality; apply Id.ap (· ⬝ _); apply mapFunctoriality;

  transitivity; apply Id.ap (_ ⬝ · ⬝ _); symmetry; apply Id.assoc;
  transitivity; apply Id.ap (· ⬝ _); apply Id.assoc;
  transitivity; symmetry; apply Id.assoc (_ ⬝ Id.ap _ _);
  transitivity; apply Id.ap (_⁻¹ ⬝ _ ⬝ ·); symmetry; apply Id.assoc;
  transitivity; apply Id.assoc (_⁻¹ ⬝ _);

  apply bimap (· ⬝ _ ⬝ ·) <;> symmetry;
  { transitivity; apply Id.ap; symmetry; apply Id.assoc;
    transitivity; apply Id.assoc; transitivity; apply Id.ap (· ⬝ _);
    apply Id.invComp; reflexivity };
  { transitivity; apply Id.ap (· ⬝ _);
    transitivity; apply Id.explodeInv; apply Id.ap; apply Id.explodeInv;
    transitivity; apply Id.ap (· ⬝ _); apply Id.assoc;
    transitivity; symmetry; apply Id.assoc;
    transitivity; apply Id.ap; apply Id.invComp;
    transitivity; apply Id.reflRight; apply bimap;
    { transitivity; apply Id.ap; apply Id.mapInv; apply Id.invInv };
    { apply Id.invInv } }
end

noncomputable hott def diffComHom {A : Type u} {B : Type v} {C : Type w}
  (f : B → C) (g : A → B) {x : A} (ε : 𝔻 x) : d (f ∘ g) x ε = d f (g x) (d g x ε) :=
Id.ap (Sigma.mk _) (infProxApCom f g _)

hott def diffCom {A : Type u} {B : Type v} {C : Type w} (f : B → C) (g : A → B)
  {x : A} : d (f ∘ g) x = (d f) (g x) ∘ d g x :=
Theorems.funext (diffComHom f g)

noncomputable hott def diffIdfun {A : Type u} (x : A) (ε : 𝔻 x) : d idfun x ε = ε :=
Id.ap (Sigma.mk _) (infProxApIdp _)

hott def isHomogeneous (A : Type u) :=
Σ (e : A) (t : Π x, A ≃ A), Π x, t x e = x

hott def Homogeneous :=
Σ (A : Type u), isHomogeneous A

noncomputable instance : Coe Homogeneous (Type u) := ⟨Sigma.fst⟩

hott def Homogeneous.cart (A B : Homogeneous) : Homogeneous :=
⟨A.1 × B.1, ⟨(A.2.1, B.2.1), λ w, prodEquiv (A.2.2.1 w.1) (B.2.2.1 w.2),
             λ w, Product.prod (A.2.2.2 w.1) (B.2.2.2 w.2)⟩⟩

instance : HMul Homogeneous Homogeneous Homogeneous := ⟨Homogeneous.cart⟩

end GroundZero.HITs.Infinitesimal