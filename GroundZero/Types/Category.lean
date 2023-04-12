import GroundZero.Types.Precategory
open GroundZero.Types.Equiv
open GroundZero.Structures

namespace GroundZero.Types
universe u v

def Category (A : Type u) :=
Σ (𝒞 : Precategory A), Π a b, biinv (@Precategory.idtoiso A 𝒞 a b)

namespace Category
  variable {A : Type u} (𝒞 : Category A)
  def hom := 𝒞.1.hom

  def set : Π (x y : A), hset (hom 𝒞 x y) := 𝒞.1.set

  def id : Π {a : A}, hom 𝒞 a a := 𝒞.1.id
  def comp {A : Type u} {𝒞 : Category A} {a b c : A}
    (f : hom 𝒞 b c) (g : hom 𝒞 a b) : hom 𝒞 a c :=
  𝒞.1.comp f g
 
  local infix:60 " ∘ " => comp

  def idLeft : Π {a b : A} (f : hom 𝒞 a b), f = id 𝒞 ∘ f := 𝒞.1.idLeft
  def idRight : Π {a b : A} (f : hom 𝒞 a b), f = f ∘ id 𝒞 := 𝒞.1.idRight
  def assoc : Π {a b c d : A} (f : hom 𝒞 a b) (g : hom 𝒞 b c) (h : hom 𝒞 c d), h ∘ (g ∘ f) = (h ∘ g) ∘ f := 𝒞.1.assoc

  def iso (a b : A) := Precategory.iso 𝒞.1 a b

  hott def idtoiso {a b : A} : a = b → iso 𝒞 a b :=
  Precategory.idtoiso 𝒞.1

  hott def univalence {a b : A} : (a = b) ≃ (iso 𝒞 a b) :=
  ⟨idtoiso 𝒞, 𝒞.snd a b⟩

  hott def ua {a b : A} : iso 𝒞 a b → a = b :=
  (univalence 𝒞).left

  hott def uaβrule₁ {a b : A} (φ : iso 𝒞 a b) : idtoiso 𝒞 (ua 𝒞 φ) = φ :=
  (univalence 𝒞).forwardLeft φ

  hott def uaβrule₂ {a b : A} (φ : a = b) : ua 𝒞 (idtoiso 𝒞 φ) = φ :=
  (univalence 𝒞).leftForward φ

  def Mor {A : Type u} (𝒞 : Category A) := Σ (x y : A), hom 𝒞 x y

  def twoOutOfThree {a b c : A} (g : hom 𝒞 b c) (f : hom 𝒞 a b) (K : Π (x y : A), hom 𝒞 x y → Type v) :=
  (K a b f → K b c g → K a c (g ∘ f)) × (K a c (g ∘ f) → K b c g → K a b f) × (K a b f → K a c (g ∘ f) → K b c g)
end Category

end GroundZero.Types