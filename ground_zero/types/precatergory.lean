import ground_zero.HITs.graph ground_zero.HITs.interval
open ground_zero.HITs ground_zero.types ground_zero.theorems.functions
open ground_zero.HITs.interval ground_zero.types.equiv

hott theory

namespace ground_zero.types
universes u v

structure precategory (α : Sort u) :=
(hom : α → α → Sort v)
(id {a : α} : hom a a)
(comp {a b c : α} : hom b c → hom a b → hom a c)
(infix ∘ := comp)
(id_left {a b : α} : Π (f : hom a b), f = id ∘ f)
(id_right {a b : α} : Π (f : hom a b), f = f ∘ id)
(assoc {a b c d : α} : Π (f : hom a b) (g : hom b c) (h : hom c d),
  h ∘ (g ∘ f) = (h ∘ g) ∘ f)

namespace precategory
  def cat_graph {α : Sort u} (𝒞 : precategory α) := graph (hom 𝒞)

  def Path (α : Sort u) : precategory α :=
  { hom := (=),
    id := ground_zero.types.eq.refl,
    comp := λ a b c p q, q ⬝ p,
    id_left := λ a b p, (eq.refl_right p)⁻¹,
    id_right := λ a b p, (eq.refl_left p)⁻¹,
    assoc := λ a b c d f g h, (eq.assoc f g h)⁻¹ }

  def Top : precategory (Sort u) :=
  { hom := (→),
    id := @idfun,
    comp := @function.comp,
    id_left := λ a b f, funext (homotopy.id f),
    id_right := λ a b f, funext (homotopy.id f),
    assoc := λ a b c d f g h, eq.rfl }
end precategory

end ground_zero.types