import GroundZero.Types.Precategory

open GroundZero.Types.Precategory (idtoiso)
open GroundZero.Types.Equiv
open GroundZero.Structures

namespace GroundZero.Types
universe u v

hott definition Category :=
Σ (A : Precategory), Π a b, biinv (@idtoiso A a b)

namespace Category
  variable (A : Category)

  hott abbreviation obj := A.1.obj
  hott abbreviation hom := A.1.hom

  hott definition set : Π (x y : A.obj), hset (hom A x y) := A.1.set

  attribute [irreducible] set

  hott abbreviation id : Π {a : A.obj}, hom A a a := A.1.id

  hott abbreviation comp {A : Category} {a b c : A.obj}
    (f : hom A b c) (g : hom A a b) : hom A a c :=
  A.1.com f g

  local infix:60 " ∘ " => comp

  hott abbreviation lu    : Π {a b : A.obj} (f : hom A a b), id A ∘ f = f := A.1.lu
  hott abbreviation ru    : Π {a b : A.obj} (f : hom A a b), f ∘ id A = f := A.1.ru
  hott abbreviation assoc : Π {a b c d : A.obj} (f : hom A a b) (g : hom A b c) (h : hom A c d), h ∘ (g ∘ f) = (h ∘ g) ∘ f := A.1.assoc

  hott abbreviation iso (a b : A.obj) := Precategory.iso A.1 a b

  hott abbreviation idtoiso {a b : A.obj} : a = b → iso A a b :=
  Precategory.idtoiso A.1

  hott definition univalence {a b : A.obj} : (a = b) ≃ (iso A a b) :=
  ⟨idtoiso A, A.snd a b⟩

  hott definition ua {a b : A.obj} : iso A a b → a = b :=
  (univalence A).left

  hott definition uaβrule₁ {a b : A.obj} (φ : iso A a b) : idtoiso A (ua A φ) = φ :=
  (univalence A).forwardLeft φ

  hott definition uaβrule₂ {a b : A.obj} (φ : a = b) : ua A (idtoiso A φ) = φ :=
  (univalence A).leftForward φ

  hott definition Mor (A : Category) := Σ (x y : A.obj), hom A x y

  hott definition twoOutOfThree {a b c : A.obj} (g : hom A b c) (f : hom A a b) (K : Π (x y : A.obj), hom A x y → Type v) :=
  (K a b f → K b c g → K a c (g ∘ f)) × (K a c (g ∘ f) → K b c g → K a b f) × (K a b f → K a c (g ∘ f) → K b c g)
end Category

end GroundZero.Types
