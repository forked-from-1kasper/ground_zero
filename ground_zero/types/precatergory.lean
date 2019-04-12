import ground_zero.HITs.graph
open ground_zero.HITs ground_zero.types

namespace ground_zero.types
hott theory

universe u

structure precategory (α : Sort u) :=
(hom : α → α → Sort u)
(id {a : α} : hom a a)
(comp {a b c : α} : hom b c → hom a b → hom a c)
(infix ∘ := comp)
(id_left {a b : α} : Π (f : hom a b), f = id ∘ f)
(id_right {a b : α} : Π (f : hom a b), f = f ∘ id)
(assoc {a b c d : α} : Π (f : hom a b) (g : hom b c) (h : hom c d),
  h ∘ (g ∘ f) = (h ∘ g) ∘ f)

def cat_graph {α : Sort u} (C : precategory α) := graph C.hom

theorem type_is_precategory (α : Sort u) : precategory α :=
{ hom := (=),
  id := ground_zero.types.eq.refl,
  comp := λ a b c p q, q ⬝ p,
  id_left := λ a b p, (eq.refl_right p)⁻¹,
  id_right := λ a b p, (eq.refl_left p)⁻¹,
  assoc := λ a b c d f g h, (eq.assoc f g h)⁻¹ }

end ground_zero.types