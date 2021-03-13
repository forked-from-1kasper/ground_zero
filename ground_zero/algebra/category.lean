import ground_zero.algebra.basic
open ground_zero.types
open ground_zero

hott theory

namespace ground_zero.algebra

universe u

namespace precategory
  inductive arity : Type
  | left | right | mul | bottom
  open arity

  def signature : arity + ⊥ → ℕ
  | (sum.inl mul)    := 2
  | (sum.inl left)   := 1
  | (sum.inl right)  := 1
  | (sum.inl bottom) := 0
end precategory

def precategory : Type (u + 1) :=
Alg.{0 0 u 0} precategory.signature

namespace precategory
  variable (𝒞 : precategory.{u})

  def bottom : 𝒞.carrier :=
  𝒞.op arity.bottom ★
  notation `∄` := bottom _

  def μ : 𝒞.carrier → 𝒞.carrier → 𝒞.carrier :=
  λ x y, 𝒞.op arity.mul (x, y, ★)

  def dom : 𝒞.carrier → 𝒞.carrier :=
  λ x, 𝒞.op arity.left (x, ★)

  def cod : 𝒞.carrier → 𝒞.carrier :=
  λ x, 𝒞.op arity.right (x, ★)

  def defined (x : 𝒞.carrier) : Type u := x ≠ ∄

  def id (x : 𝒞.carrier) :=
  ∥(Σ φ, (𝒞.dom φ = x) + (𝒞.cod φ = x))∥

  def objs := Σ x, 𝒞.id x × 𝒞.defined x

  def Hom (a b : 𝒞.carrier) :=
  Σ φ, ∥(𝒞.dom φ = a) + (𝒞.cod φ = b)∥

  def monic (a : 𝒞.carrier) :=
  Π b c, 𝒞.μ a b = 𝒞.μ a c → b = c

  def epic (a : 𝒞.carrier) :=
  Π b c, 𝒞.μ b a = 𝒞.μ c a → b = c

  def bimorphism (a : 𝒞.carrier) :=
  monic 𝒞 a × epic 𝒞 a

  def following (a b : 𝒞.carrier) :=
  𝒞.dom a = 𝒞.cod b

  def endo (a : 𝒞.carrier) :=
  𝒞.following a a
end precategory

/-
  MacLane, S.: Categories for the Working Mathematician. Springer-Verlag, New York (1971).
  Similar axioms can be found in XII, 5. Single-Set Categories.
-/
class category (𝒞 : precategory) :=
(bottom_left  : Π a, 𝒞.μ ∄ a = ∄)
(bottom_right : Π a, 𝒞.μ a ∄ = ∄)
(bottom_dom   : 𝒞.dom ∄ = ∄)
(bottom_cod   : 𝒞.cod ∄ = ∄)
(dom_comp     : Π a, 𝒞.μ a (𝒞.dom a) = a)
(cod_comp     : Π a, 𝒞.μ (𝒞.cod a) a = a)
(mul_dom      : Π a b, 𝒞.dom (𝒞.μ a b) = 𝒞.dom b)
(mul_cod      : Π a b, 𝒞.cod (𝒞.μ a b) = 𝒞.cod a)
(dom_cod      : 𝒞.dom ∘ 𝒞.cod ~ 𝒞.cod)
(cod_dom      : 𝒞.cod ∘ 𝒞.dom ~ 𝒞.dom)
(mul_assoc    : Π a b c, 𝒞.μ (𝒞.μ a b) c = 𝒞.μ a (𝒞.μ b c))
(mul_def      : Π a b, 𝒞.defined a → 𝒞.defined b →
                       𝒞.defined (𝒞.μ a b) = 𝒞.following a b)

namespace category
  variables {𝒞 : precategory} [category 𝒞]

  @[hott] def dom_dom : 𝒞.dom ∘ 𝒞.dom ~ 𝒞.dom :=
  begin
    intro x, symmetry, transitivity, apply Id.map 𝒞.dom,
    symmetry, apply dom_comp, apply mul_dom
  end

  @[hott] def cod_cod : 𝒞.cod ∘ 𝒞.cod ~ 𝒞.cod :=
  begin
    intro x, symmetry, transitivity, apply Id.map 𝒞.cod,
    symmetry, apply cod_comp, apply mul_cod
  end

  @[hott] def cod_mul_cod : Π a, 𝒞.μ (𝒞.cod a) (𝒞.cod a) = 𝒞.cod a :=
  begin
    intro a, transitivity, apply Id.map (λ b, 𝒞.μ b (𝒞.cod a)),
    symmetry, apply cod_cod, apply cod_comp
  end

  @[hott] def dom_mul_dom : Π a, 𝒞.μ (𝒞.dom a) (𝒞.dom a) = 𝒞.dom a :=
  begin
    intro a, transitivity, apply Id.map (𝒞.μ (𝒞.dom a)),
    symmetry, apply dom_dom, apply dom_comp
  end

  @[hott] def dom_endo : Π a, 𝒞.endo (𝒞.dom a) :=
  λ x, (dom_dom x) ⬝ (cod_dom x)⁻¹

  @[hott] def cod_endo : Π a, 𝒞.endo (𝒞.cod a) :=
  λ x, (dom_cod x) ⬝ (cod_cod x)⁻¹

  @[hott] def id_endo (a : 𝒞.carrier) : 𝒞.id a → 𝒞.endo a :=
  begin
    fapply HITs.merely.rec, { apply 𝒞.hset },
    { intro φ, induction φ with φ p, change _ = _,
      induction p; induction p, apply dom_endo, apply cod_endo }
  end
end category

end ground_zero.algebra