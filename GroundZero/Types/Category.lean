import GroundZero.Types.Precategory
open GroundZero.Types.Equiv
open GroundZero.Structures

namespace GroundZero.Types
universe u v

def Category (A : Type u) :=
Ξ£ (π : Precategory A), Ξ  a b, biinv (@Precategory.idtoiso A π a b)

namespace Category
  variable {A : Type u} (π : Category A)
  def hom := π.1.hom

  def set : Ξ  (x y : A), hset (hom π x y) := π.1.set

  def id : Ξ  {a : A}, hom π a a := π.1.id
  def comp {A : Type u} {π : Category A} {a b c : A}
    (f : hom π b c) (g : hom π a b) : hom π a c :=
  π.1.comp f g
 
  local infix:60 " β " => comp

  def idLeft : Ξ  {a b : A} (f : hom π a b), f = id π β f := π.1.idLeft
  def idRight : Ξ  {a b : A} (f : hom π a b), f = f β id π := π.1.idRight
  def assoc : Ξ  {a b c d : A} (f : hom π a b) (g : hom π b c) (h : hom π c d), h β (g β f) = (h β g) β f := π.1.assoc

  def iso (a b : A) := Precategory.iso π.1 a b

  hott def idtoiso {a b : A} : a = b β iso π a b :=
  Precategory.idtoiso π.1

  hott def univalence {a b : A} : (a = b) β (iso π a b) :=
  β¨idtoiso π, π.snd a bβ©

  hott def ua {a b : A} : iso π a b β a = b :=
  (univalence π).left

  hott def uaΞ²ruleβ {a b : A} (Ο : iso π a b) : idtoiso π (ua π Ο) = Ο :=
  (univalence π).forwardLeft Ο

  hott def uaΞ²ruleβ {a b : A} (Ο : a = b) : ua π (idtoiso π Ο) = Ο :=
  (univalence π).leftForward Ο

  def Mor {A : Type u} (π : Category A) := Ξ£ (x y : A), hom π x y

  instance {A : Type u} (π : Category A) {x y : A} : Coe (hom π x y) (Mor π) :=
  β¨Ξ» f, β¨x, y, fβ©β©

  def twoOutOfThree {a b c : A} (g : hom π b c) (f : hom π a b) (K : Mor π β Type v) :=
  (K f β K g β K (g β f)) Γ (K (g β f) β K g β K f) Γ (K f β K (g β f) β K g)

  hott def isProduct (a b c : A) :=
  Ξ£ (Ο : hom π c a Γ hom π c b),
    Ξ  (x : A) (fβ : hom π x a) (fβ : hom π x b),
      contr (Ξ£ (f : hom π x c), Ο.1 β f = fβ Γ Ο.snd β f = fβ)

  hott def Product (a b : A) := Ξ£ c, isProduct π a b c
end Category

end GroundZero.Types