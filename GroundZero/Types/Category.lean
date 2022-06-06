import GroundZero.Types.Precategory
open GroundZero.Types.Equiv
open GroundZero.Structures

namespace GroundZero.Types
universe u v

def Category (α : Type u) :=
Σ (𝒞 : Precategory α), Π a b, biinv (@Precategory.idtoiso α 𝒞 a b)

namespace Category
  variable {α : Type u} (𝒞 : Category α)
  def hom := 𝒞.1.hom

  def set : Π (x y : α), hset (hom 𝒞 x y) := 𝒞.1.set

  def id : Π {a : α}, hom 𝒞 a a := 𝒞.1.id
  def comp {α : Type u} {𝒞 : Category α} {a b c : α}
    (f : hom 𝒞 b c) (g : hom 𝒞 a b) : hom 𝒞 a c :=
  𝒞.1.comp f g
 
  local infix:60 " ∘ " => comp

  def idLeft : Π {a b : α} (f : hom 𝒞 a b), f = id 𝒞 ∘ f := 𝒞.1.idLeft
  def idRight : Π {a b : α} (f : hom 𝒞 a b), f = f ∘ id 𝒞 := 𝒞.1.idRight
  def assoc : Π {a b c d : α} (f : hom 𝒞 a b) (g : hom 𝒞 b c) (h : hom 𝒞 c d), h ∘ (g ∘ f) = (h ∘ g) ∘ f := 𝒞.1.assoc

  def iso (a b : α) := Precategory.iso 𝒞.1 a b

  hott def idtoiso {a b : α} : a = b → iso 𝒞 a b :=
  Precategory.idtoiso 𝒞.1

  hott def univalence {a b : α} : (a = b) ≃ (iso 𝒞 a b) :=
  ⟨idtoiso 𝒞, 𝒞.snd a b⟩

  hott def ua {a b : α} : iso 𝒞 a b → a = b :=
  (univalence 𝒞).left

  hott def uaβrule₁ {a b : α} (φ : iso 𝒞 a b) : idtoiso 𝒞 (ua 𝒞 φ) = φ :=
  (univalence 𝒞).forwardLeft φ

  hott def uaβrule₂ {a b : α} (φ : a = b) : ua 𝒞 (idtoiso 𝒞 φ) = φ :=
  (univalence 𝒞).leftForward φ

  def Mor {α : Type u} (𝒞 : Category α) := Σ (x y : α), hom 𝒞 x y

  instance {α : Type u} (𝒞 : Category α) {x y : α} : Coe (hom 𝒞 x y) (Mor 𝒞) :=
  ⟨λ f, ⟨x, y, f⟩⟩

  def twoOutOfThree {a b c : α} (g : hom 𝒞 b c) (f : hom 𝒞 a b) (K : Mor 𝒞 → Type v) :=
  (K f → K g → K (g ∘ f)) × (K (g ∘ f) → K g → K f) × (K f → K (g ∘ f) → K g)

  hott def isProduct (a b c : α) :=
  Σ (π : hom 𝒞 c a × hom 𝒞 c b),
    Π (x : α) (f₁ : hom 𝒞 x a) (f₂ : hom 𝒞 x b),
      contr (Σ (f : hom 𝒞 x c), π.1 ∘ f = f₁ × π.snd ∘ f = f₂)

  hott def Product (a b : α) := Σ c, isProduct 𝒞 a b c
end Category

end GroundZero.Types