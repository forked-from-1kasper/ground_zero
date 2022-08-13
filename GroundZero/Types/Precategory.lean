import GroundZero.Theorems.Functions
import GroundZero.Theorems.Equiv

open GroundZero.Theorems.Functions
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Theorems

namespace GroundZero.Types
universe u v

structure Precategory (A : Type u) :=
(hom                 : A → A → Type v)
(set                 : Π (x y : A), hset (hom x y))
(id {a : A}          : hom a a)
(comp {a b c : A}    : hom b c → hom a b → hom a c)
(idLeft {a b : A}    : Π (f : hom a b), f = comp id f)
(idRight {a b : A}   : Π (f : hom a b), f = comp f id)
(assoc {a b c d : A} : Π (f : hom a b) (g : hom b c) (h : hom c d), comp h (comp g f) = comp (comp h g) f)

section
  variable (A : Type u) (𝒞 : Precategory A)

  instance : Reflexive  𝒞.hom := ⟨λ _, 𝒞.id⟩
  instance : Transitive 𝒞.hom := ⟨λ _ _ _ p q, 𝒞.comp q p⟩
end

namespace Precategory
  def compose {A : Type u} {𝒞 : Precategory A} {a b c : A}
    (g : hom 𝒞 b c) (f : hom 𝒞 a b) : hom 𝒞 a c :=
  𝒞.comp g f

  local infix:60 " ∘ " => compose

  def hasInv {A : Type u} (𝒞 : Precategory A) {a b : A} (f : hom 𝒞 a b) :=
  Σ (g : hom 𝒞 b a), (f ∘ g = id 𝒞) × (g ∘ f = id 𝒞)

  def iso {A : Type u} (𝒞 : Precategory A) (a b : A) :=
  Σ (f : hom 𝒞 a b), hasInv 𝒞 f

  hott def idiso {A : Type u} (𝒞 : Precategory A) {a : A} : iso 𝒞 a a :=
  let p : id 𝒞 = id 𝒞 ∘ id 𝒞 := idLeft 𝒞 (@id A 𝒞 a);
  ⟨id 𝒞, ⟨id 𝒞, (p⁻¹, p⁻¹)⟩⟩

  instance : Reflexive (iso 𝒞) := ⟨@idiso _ 𝒞⟩

  hott def idtoiso {A : Type u} (𝒞 : Precategory A)
    {a b : A} (p : a = b) : iso 𝒞 a b :=
  begin induction p; reflexivity end

  hott def invProp {A : Type u} (𝒞 : Precategory A)
    {a b : A} (f : hom 𝒞 a b) : prop (hasInv 𝒞 f) :=
  begin
    intro ⟨g', (H₁, H₂)⟩ ⟨g, (G₁, G₂)⟩;
    fapply Sigma.prod; apply calc
        g' = id 𝒞 ∘ g'    : idLeft _ _
       ... = (g ∘ f) ∘ g' : Id.map (compose · g') G₂⁻¹
       ... = g ∘ (f ∘ g') : (assoc _ _ _ _)⁻¹
       ... = g ∘ id 𝒞     : Id.map (compose g) H₁
       ... = g            : (idRight _ _)⁻¹;
    apply productProp <;> apply set
  end

  def op {A : Type u} (𝒞 : Precategory A) : Precategory A :=
  { hom      := λ a b, hom 𝒞 b a,
    set      := λ a b, set 𝒞 b a,
    id       := 𝒞.id,
    comp     := λ p q, 𝒞.comp q p,
    idLeft   := λ p, 𝒞.idRight p,
    idRight  := λ p, 𝒞.idLeft p,
    assoc    := λ f g h, (𝒞.assoc h g f)⁻¹ }

  def Path (A : Type u) (H : groupoid A) : Precategory A :=
  { hom      := @Id A,
    set      := H,
    id       := idp _,
    comp     := λ p q, q ⬝ p,
    idRight  := λ p, (Id.reflLeft p)⁻¹,
    idLeft   := λ p, (Id.reflRight p)⁻¹,
    assoc    := λ f g h, (Id.assoc f g h)⁻¹ }

  hott def univalent {A : Type u} (𝒞 : Precategory A) :=
  Π a b, biinv (@Precategory.idtoiso A 𝒞 a b)

  hott def isGroupoidIfUnivalent {A : Type u} (𝒞 : Precategory A) : univalent 𝒞 → groupoid A :=
  begin
    intros H a b; change hset (a = b); apply hsetRespectsEquiv;
    symmetry; existsi idtoiso 𝒞; apply H; apply hsetRespectsSigma;
    apply 𝒞.set; intro; apply propIsSet; apply invProp
  end

  hott def Functor {A : Type u} {B : Type v} (𝒞 : Precategory A) (𝒟 : Precategory B) :=
  Σ (F : A → B) (G : Π a b, 𝒞.hom a b → 𝒟.hom (F a) (F b)),
    (Π a, G a a 𝒞.id = 𝒟.id) × (Π a b c f g, G a c (𝒞.comp f g) = 𝒟.comp (G b c f) (G a b g))

  section
    variable {A : Type u} {B : Type v} {𝒞 : Precategory A} {𝒟 : Precategory B} (F : Functor 𝒞 𝒟)

    hott def isFaithful := Π a b, injective  (F.2.1 a b)
    hott def isFull     := Π a b, surjective (F.2.1 a b)
  end

  hott def Natural {A : Type u} {B : Type v} {𝒞 : Precategory A} {𝒟 : Precategory B} (F G : Functor 𝒞 𝒟) :=
  Σ (η : Π x, hom 𝒟 (F.1 x) (G.1 x)), Π (a b : A) (f : hom 𝒞 a b), η b ∘ F.2.1 a b f = G.2.1 a b f ∘ η a

  hott def isProduct {A : Type u} (𝒞 : Precategory A) (a b c : A) :=
  Σ (i : hom 𝒞 c a) (j : hom 𝒞 c b),
    ∀ (x : A) (f₁ : hom 𝒞 x a) (f₂ : hom 𝒞 x b),
      contr (Σ (f : hom 𝒞 x c), i ∘ f = f₁ × j ∘ f = f₂)

  hott def isCoproduct {A : Type u} (𝒞 : Precategory A) (a b c : A) :=
  isProduct (op 𝒞) a b c
end Precategory

end GroundZero.Types