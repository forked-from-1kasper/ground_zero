import ground_zero.algebra.basic
open ground_zero.types

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
  def bottom (𝒞 : precategory) : 𝒞.carrier :=
  𝒞.op arity.bottom ★

  abbreviation undefined {𝒞 : precategory} :=
  𝒞.bottom

  notation `∄` := undefined

  def μ (𝒞 : precategory) : 𝒞.carrier → 𝒞.carrier → 𝒞.carrier :=
  λ x y, 𝒞.op arity.mul (x, y, ★)

  def lid (𝒞 : precategory) : 𝒞.carrier → 𝒞.carrier :=
  λ x, 𝒞.op arity.left (x, ★)

  def rid (𝒞 : precategory) : 𝒞.carrier → 𝒞.carrier :=
  λ x, 𝒞.op arity.right (x, ★)
end precategory

class category (𝒞 : precategory) :=
(bottom_left  : Π a, 𝒞.μ ∄ a = ∄)
(bottom_right : Π a, 𝒞.μ a ∄ = ∄)
(lid_comp     : Π a, 𝒞.μ (𝒞.lid a) a = a)
(rid_comp     : Π a, 𝒞.μ a (𝒞.rid a) = a)
(lid_lid      : 𝒞.lid ∘ 𝒞.lid ~ 𝒞.lid)
(rid_rid      : 𝒞.rid ∘ 𝒞.rid ~ 𝒞.rid)
(lid_rid      : 𝒞.lid ∘ 𝒞.rid ~ 𝒞.rid)
(rid_lid      : 𝒞.rid ∘ 𝒞.lid ~ 𝒞.lid)
(mul_assoc    : Π a b c, 𝒞.μ (𝒞.μ a b) c = 𝒞.μ a (𝒞.μ b c))

end ground_zero.algebra