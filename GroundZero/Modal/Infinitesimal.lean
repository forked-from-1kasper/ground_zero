import GroundZero.Types.Equiv

open GroundZero.Types.Equiv (biinv)
open GroundZero.Types
open GroundZero.Proto

/-
  Infinitesimal shape modality or coreduction.

  https://github.com/forked-from-1kasper/anders/blob/master/library/modal/infinitesimal.anders
  https://www.math.kit.edu/iag3/~wellen/media/diss.pdf
  https://arxiv.org/pdf/1806.05966.pdf

  * HoTT 7.7 Modalities
-/

namespace GroundZero.HITs.Infinitesimal
universe u v w

axiom Im : Type u → Type u
notation "ℑ" => Im

axiom ι {A : Type u} : A → ℑ A
axiom μ {A : Type u} : ℑ (ℑ A) → ℑ A

axiom μcom {A : Type u} : μ ∘ ι ~ @idfun (ℑ A)
axiom ιcoh {A : Type u} : ι ∘ μ ~ @idfun (ℑ (ℑ A))

section
  variable {A : Type u} {B : ℑ A → Type v}

  axiom Im.ind (f : Π x, ℑ (B (ι x))) : Π x, ℑ (B x)
  axiom Im.indβrule {f : Π x, ℑ (B (ι x))} (a : A) : Im.ind f (ι a) = f a
end

axiom κ {A : Type u} {a b : ℑ A} : ℑ (a = b) → a = b
axiom κ.idp {A : Type u} {a : ℑ A} : κ (ι (idp a)) = idp a

noncomputable hott def κ.right {A : Type u} {a b : ℑ A} : @κ A a b ∘ ι ~ idfun :=
@Id.rec (ℑ A) a (λ b p, κ (ι p) = p) κ.idp b

noncomputable hott def κ.left {A : Type u} {a b : ℑ A} : ι ∘ @κ A a b ~ idfun :=
λ ρ, κ (@Im.ind (a = b) (λ ρ, ι (κ ρ) = ρ) (λ p, ι (Id.map ι (κ.right p))) ρ)

hott def isCoreduced (A : Type u) := biinv (@ι A)

noncomputable hott def Im.coreduced (A : Type u) : isCoreduced (ℑ A) :=
Qinv.toBiinv ι ⟨μ, (ιcoh, μcom)⟩

noncomputable hott def Im.idCoreduced {A : Type u} (a b : ℑ A) : isCoreduced (a = b) :=
Qinv.toBiinv ι ⟨κ, (κ.left, κ.right)⟩

noncomputable hott def Im.indε {A : Type u} {B : ℑ A → Type v} (η : Π i, isCoreduced (B i))
  (f : Π x, B (ι x)) : Π x, B x :=
λ a, (η a).1.1 (@Im.ind A B (λ x, ι (f x)) a)

noncomputable def Im.indεβrule {A : Type u} {B : ℑ A → Type v} (η : Π i, isCoreduced (B i))
  (f : Π x, B (ι x)) : Π x, Im.indε η f (ι x) = f x :=
λ a, Id.map (η (ι a)).1.1 (Im.indβrule a) ⬝ (η (ι a)).1.2 (f a)

noncomputable section
  variable {A : Type u} {B : Type v} (f : A → ℑ B)

  hott def Im.rec : Im A → ℑ B := Im.ind f
  hott def Im.recβrule : Π x, Im.rec f (ι x) = f x := Im.indβrule
end

noncomputable section
  variable {A : Type u} {B : Type v} (η : isCoreduced B) (f : A → B)

  hott def Im.recε : Im A → B := Im.indε (λ _, η) f

  hott def Im.recεβrule : Π x, Im.recε η f (ι x) = f x :=
  Im.indεβrule (λ _, η) f
end

noncomputable section
  variable {A : Type u} {B : Type v} (f : A → B)

  hott def Im.ap : ℑ A → ℑ B := Im.rec (ι ∘ f)

  hott def Im.naturality (x : A) : Im.ap f (ι x) = ι (f x) := Im.recβrule _ x
end

noncomputable hott def Im.apIdfun {A : Type u} : @idfun (ℑ A) ~ Im.ap idfun :=
Im.indε (λ _, Im.idCoreduced _ _) (λ _, (Im.naturality idfun _)⁻¹)

noncomputable hott def Im.apCom {A : Type u} {B : Type v} {C : Type w}
  (f : B → C) (g : A → B) : Im.ap (f ∘ g) ~ Im.ap f ∘ Im.ap g :=
Im.indε (λ _, Im.idCoreduced _ _) (λ _, Im.naturality _ _
                                     ⬝ (Im.naturality f _)⁻¹
                                     ⬝  Id.map (ap f) (Im.naturality g _)⁻¹)

end GroundZero.HITs.Infinitesimal