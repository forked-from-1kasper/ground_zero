import ground_zero.HITs.graph ground_zero.structures
open ground_zero.HITs ground_zero.types ground_zero.theorems.functions
open ground_zero.HITs.interval ground_zero.types.equiv ground_zero.structures

hott theory

namespace ground_zero.types
universes u v

structure precategory (α : Type u) :=
(hom : α → α → Type v)
(set : Π {x y : α}, hset (hom x y))
(id {a : α} : hom a a)
(comp {a b c : α} : hom b c → hom a b → hom a c)
(infix ∘ := comp)
(id_left {a b : α} : Π (f : hom a b), f = id ∘ f)
(id_right {a b : α} : Π (f : hom a b), f = f ∘ id)
(assoc {a b c d : α} : Π (f : hom a b) (g : hom b c) (h : hom c d),
  h ∘ (g ∘ f) = (h ∘ g) ∘ f)

namespace precategory
  def cat_graph {α : Type u} (𝒞 : precategory α) := graph (hom 𝒞)

  def Mor {α : Type u} (𝒞 : precategory α) := Σ (x y : α), hom 𝒞 x y

  instance {α : Type u} (𝒞 : precategory α) {x y : α} : has_coe (hom 𝒞 x y) (Mor 𝒞) :=
  ⟨λ f, ⟨x, y, f⟩⟩

  def compose {α : Type u} {𝒞 : precategory α} {a b c : α}
    (g : hom 𝒞 b c) (f : hom 𝒞 a b) : hom 𝒞 a c := 𝒞.comp g f
  local infix ∘ := compose

  def two_out_of_three {α : Type u} (𝒞 : precategory α) {a b c : α}
    (g : hom 𝒞 b c) (f : hom 𝒞 a b) (K : Mor 𝒞 → Type v) :=
  (K f → K g → K (g ∘ f)) ×
  (K (g ∘ f) → K g → K f) ×
  (K f → K (g ∘ f) → K g)

  def has_inv {α : Type u} (𝒞 : precategory α) {x y : α} (f : hom 𝒞 x y) :=
  Σ (g : hom 𝒞 y x), (f ∘ g = id 𝒞) × (g ∘ f = id 𝒞)

  def iso {α : Type u} (𝒞 : precategory α) (x y : α) :=
  Σ (f : hom 𝒞 x y), has_inv 𝒞 f

  def op {α : Type u} (𝒞 : precategory α) : precategory α :=
  { hom := λ a b, hom 𝒞 b a,
    set := λ a b p q, set 𝒞,
    id := 𝒞.id,
    comp := λ a b c p q, 𝒞.comp q p,
    id_left := λ a b p, 𝒞.id_right p,
    id_right := λ a b p, 𝒞.id_left p,
    assoc := λ a b c d f g h, (𝒞.assoc h g f)⁻¹ }

  postfix `ᵒᵖ`:1025 := op

  def Path (α : Type u) (h : groupoid α) : precategory α :=
  { hom := (=),
    set := λ a b p q, h,
    id := ground_zero.types.eq.refl,
    comp := λ a b c p q, q ⬝ p,
    id_left := λ a b p, (eq.refl_right p)⁻¹,
    id_right := λ a b p, (eq.refl_left p)⁻¹,
    assoc := λ a b c d f g h, (eq.assoc f g h)⁻¹ }

  def sigma_unique {α : Type u} (π : α → Type v) :=
  Σ x, (π x) × (Π y, π y → y = x)
  notation `Σ!` binders `, ` r:(scoped P, sigma_unique P) := r

  structure product {α : Type u} (𝒞 : precategory α) (X₁ X₂ : α) :=
  (X : α) (π₁ : hom 𝒞 X X₁) (π₂ : hom 𝒞 X X₂)
  (canonicity : Π (Y : α) (f₁ : hom 𝒞 Y X₁) (f₂ : hom 𝒞 Y X₂),
    Σ! (f : hom 𝒞 Y X), π₁ ∘ f = f₁ × π₂ ∘ f = f₂)

  def coproduct {α : Type u} (𝒞 : precategory α) (X₁ X₂ : α) :=
  product 𝒞ᵒᵖ X₁ X₂
end precategory

end ground_zero.types