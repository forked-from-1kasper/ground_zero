import ground_zero.theorems.prop
open ground_zero.theorems
open ground_zero.structures

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

attribute [refl] precategory.id
attribute [trans] precategory.comp

namespace precategory
  def compose {α : Type u} {𝒞 : precategory α} {a b c : α}
    (g : hom 𝒞 b c) (f : hom 𝒞 a b) : hom 𝒞 a c := 𝒞.comp g f
  local infix ∘ := compose

  def has_inv {α : Type u} (𝒞 : precategory α) {a b : α} (f : hom 𝒞 a b) :=
  Σ (g : hom 𝒞 b a), (f ∘ g = id 𝒞) × (g ∘ f = id 𝒞)

  def iso {α : Type u} (𝒞 : precategory α) (a b : α) :=
  Σ (f : hom 𝒞 a b), has_inv 𝒞 f

  @[hott] def idtoiso {α : Type u} (𝒞 : precategory α)
    {a b : α} (p : a = b) : hom 𝒞 a b :=
  begin induction p, refl end

  @[hott] def inv_prop {α : Type u} (𝒞 : precategory α) {a b : α}
    (f : hom 𝒞 a b) : prop (has_inv 𝒞 f) := begin
    intros p q, induction p with g' H, induction q with g G,
    induction H with H₁ H₂, induction G with G₁ G₂,
    fapply sigma.prod, calc
        g' = id 𝒞 ∘ g' : by apply id_left
       ... = (g ∘ f) ∘ g' : (∘ g') # G₂⁻¹
       ... = g ∘ (f ∘ g') : begin symmetry, apply assoc end
       ... = g ∘ id 𝒞 : (compose g) # H₁
       ... = g : begin symmetry, apply id_right end,
    apply prop.product_prop; apply set
  end

  def op {α : Type u} (𝒞 : precategory α) : precategory α :=
  ⟨λ a b, hom 𝒞 b a,
   λ a b p q, set 𝒞,
   𝒞.id,
   λ a b c p q, 𝒞.comp q p,
   λ a b p, 𝒞.id_right p,
   λ a b p, 𝒞.id_left p,
   λ a b c d f g h, (𝒞.assoc h g f)⁻¹⟩

  def Path (α : Type u) (h : groupoid α) : precategory α :=
  ⟨(=),
   λ a b p q, h,
   ground_zero.types.eq.refl,
   λ a b c p q, q ⬝ p,
   λ a b p, (eq.refl_right p)⁻¹,
   λ a b p, (eq.refl_left p)⁻¹,
   λ a b c d f g h, (eq.assoc f g h)⁻¹⟩

  def sigma_unique {α : Type u} (π : α → Type v) :=
  Σ x, (π x) × (Π y, π y → y = x)
  notation `Σ!` binders `, ` r:(scoped P, sigma_unique P) := r

  structure product {α : Type u} (𝒞 : precategory α) (X₁ X₂ : α) :=
  (X : α) (π₁ : hom 𝒞 X X₁) (π₂ : hom 𝒞 X X₂)
  (canonicity : Π (Y : α) (f₁ : hom 𝒞 Y X₁) (f₂ : hom 𝒞 Y X₂),
    Σ! (f : hom 𝒞 Y X), π₁ ∘ f = f₁ × π₂ ∘ f = f₂)

  def coproduct {α : Type u} (𝒞 : precategory α) (X₁ X₂ : α) :=
  product (op 𝒞) X₁ X₂
end precategory

end ground_zero.types