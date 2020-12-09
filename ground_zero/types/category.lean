import ground_zero.types.precategory
open ground_zero.structures

namespace ground_zero.types
hott theory

universes u v

def category (α : Type u) :=
Σ (𝒞 : precategory α), Π a b,
  equiv.biinv (@precategory.idtoiso α 𝒞 a b)

namespace category
  variables {α : Type u} (𝒞 : category α)

  def hom := 𝒞.fst.hom
  def set : Π {x y : α}, hset (hom 𝒞 x y) := 𝒞.fst.set
  @[refl] def id : Π {a : α}, hom 𝒞 a a := 𝒞.fst.id
  @[trans] def comp {α : Type u} {𝒞 : category α} {a b c : α}
    (f : hom 𝒞 b c) (g : hom 𝒞 a b) : hom 𝒞 a c :=
  𝒞.fst.comp f g
  local infix ∘ := comp

  def id_left : Π {a b : α} (f : hom 𝒞 a b), f = id 𝒞 ∘ f := 𝒞.fst.id_left
  def id_right : Π {a b : α} (f : hom 𝒞 a b), f = f ∘ id 𝒞 := 𝒞.fst.id_right
  def assoc : Π {a b c d : α} (f : hom 𝒞 a b) (g : hom 𝒞 b c) (h : hom 𝒞 c d),
    h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
  𝒞.fst.assoc

  def iso (a b : α) := precategory.iso 𝒞.fst a b

  @[hott] def idtoiso {a b : α} : a = b → iso 𝒞 a b :=
  precategory.idtoiso 𝒞.fst

  @[hott] def univalence {a b : α} : (a = b) ≃ (iso 𝒞 a b) :=
  ⟨idtoiso 𝒞, 𝒞.snd a b⟩

  @[hott] def ua {a b : α} : iso 𝒞 a b → a = b :=
  (univalence 𝒞).left

  @[hott] def uaβrule₁ {a b : α} (φ : iso 𝒞 a b) : idtoiso 𝒞 (ua 𝒞 φ) = φ :=
  (univalence 𝒞).forward_left φ

  @[hott] def uaβrule₂ {a b : α} (φ : a = b) : ua 𝒞 (idtoiso 𝒞 φ) = φ :=
  (univalence 𝒞).left_forward φ

  def Mor {α : Type u} (𝒞 : category α) := Σ (x y : α), hom 𝒞 x y

  instance {α : Type u} (𝒞 : category α) {x y : α} :
    has_coe (hom 𝒞 x y) (Mor 𝒞) :=
  ⟨λ f, ⟨x, y, f⟩⟩

  def two_out_of_three {a b c : α}
    (g : hom 𝒞 b c) (f : hom 𝒞 a b) (K : Mor 𝒞 → Type v) :=
  (K f → K g → K (g ∘ f)) ×
  (K (g ∘ f) → K g → K f) ×
  (K f → K (g ∘ f) → K g)

  @[hott] def is_product (a b c : α) :=
  Σ (π : hom 𝒞 c a × hom 𝒞 c b),
    Π (x : α) (f₁ : hom 𝒞 x a) (f₂ : hom 𝒞 x b),
      contr (Σ (f : hom 𝒞 x c), π.fst ∘ f = f₁ × π.snd ∘ f = f₂)

  @[hott] def Product (a b : α) := Σ c, is_product 𝒞 a b c
end category

end ground_zero.types