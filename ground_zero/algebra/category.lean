import ground_zero.algebra.basic ground_zero.theorems.classical
open ground_zero.types.equiv (transport)
open ground_zero.structures (hset prop)
open ground_zero.theorems
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
  @[hott] def intro {α : Type u} (p : hset α) (μ : α → α → α)
    (dom cod : α → α) (bot : α) : precategory.{u} :=
  begin
    existsi zeroeqv (λ _ _, p), split; intro i; induction i,
    exact λ ⟨a, _⟩, dom a, exact λ ⟨a, _⟩, cod a,
    exact λ ⟨a, b, _⟩, μ a b, exact λ _, bot
  end

  variable (𝒞 : precategory.{u})

  def bottom : 𝒞.carrier :=
  𝒞.op arity.bottom ★
  notation `∄` := bottom _

  def μ : 𝒞.carrier → 𝒞.carrier → 𝒞.carrier :=
  λ x y, 𝒞.op arity.mul (x, y, ★)

  def dom : 𝒞 →ᴬ 𝒞 :=
  λ x, 𝒞.op arity.left (x, ★)

  def cod : 𝒞 →ᴬ 𝒞 :=
  λ x, 𝒞.op arity.right (x, ★)

  def defined (x : 𝒞.carrier) : Type u := x ≠ ∄
  prefix `∃` := defined _

  def id (x : 𝒞.carrier) := x = 𝒞.dom x

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

  def retraction (a b : 𝒞.carrier) :=
  𝒞.μ a b = 𝒞.cod a

  def coretraction (a b : 𝒞.carrier) :=
  𝒞.μ a b = 𝒞.dom a

  def biinv (a b : 𝒞.carrier) :=
  retraction 𝒞 a b × coretraction 𝒞 a b

  @[hott] def biinv.prop {a b : 𝒞.carrier} : prop (biinv 𝒞 a b) :=
  begin fapply structures.product_prop; apply 𝒞.hset end

  def iso (a : 𝒞.carrier) :=
  Σ b, biinv 𝒞 a b

  def auto (a : 𝒞.carrier) :=
  endo 𝒞 a × iso 𝒞 a

  @[hott] def op : precategory :=
  intro (λ _ _, 𝒞.hset) (λ a b, 𝒞.μ b a) 𝒞.cod 𝒞.dom ∄
  postfix `ᵒᵖ`:2000 := op

  -- Homomoprhism of algebras is a functor here
  variables (𝒟 : precategory) (f : 𝒞 ⤳ 𝒟)

  @[hott] def functor_comp :
    Π a b, f.ap (𝒞.μ a b) = 𝒟.μ (f.ap a) (f.ap b) :=
  λ a b, f.snd.fst arity.mul (a, b, ★)

  @[hott] def functor_dom : Π a, f.ap (𝒞.dom a) = 𝒟.dom (f.ap a) :=
  λ a, f.snd.fst arity.left (a, ★)

  @[hott] def functor_cod : Π a, f.ap (𝒞.cod a) = 𝒟.cod (f.ap a) :=
  λ a, f.snd.fst arity.right (a, ★)

  @[hott] def functor_bottom : f.ap ∄ = ∄ :=
  f.snd.fst arity.bottom ★
end precategory

/-
  MacLane, S.: Categories for the Working Mathematician. Springer-Verlag, New York (1971).
  Similar axioms can be found in XII. 5. Single-Set Categories.
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
(mul_def      : Π a b, ∃a → ∃b → (∃(𝒞.μ a b) ↔ 𝒞.following a b))

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

  @[hott] def undef_dom_impl_undef {a : 𝒞.carrier} : 𝒞.dom a = ∄ → a = ∄ :=
  begin
    intro p, transitivity, apply (dom_comp a)⁻¹,
    transitivity, apply Id.map (𝒞.μ a) p, apply bottom_right
  end

  @[hott] def undef_cod_impl_undef {a : 𝒞.carrier} : 𝒞.cod a = ∄ → a = ∄ :=
  begin
    intro p, transitivity, apply (cod_comp a)⁻¹,
    transitivity, apply Id.map (λ b, 𝒞.μ b a) p, apply bottom_left
  end

  @[hott] def dom_def {a : 𝒞.carrier} : ∃a → ∃(𝒞.dom a) :=
  begin
    apply classical.contrapos.intro,
    repeat { apply 𝒞.hset },
    apply undef_dom_impl_undef
  end

  @[hott] def cod_def {a : 𝒞.carrier} : ∃a → ∃(𝒞.cod a) :=
  begin
    apply classical.contrapos.intro,
    repeat { apply 𝒞.hset },
    apply undef_cod_impl_undef
  end

  @[hott] def id_mul_id {a : 𝒞.carrier} : 𝒞.id a → 𝒞.μ a a = a :=
  λ p, @transport _ (λ x, 𝒞.μ x x = x) (𝒞.dom a) a p⁻¹ (dom_mul_dom a)

  @[hott] def dom_endo : Π a, 𝒞.endo (𝒞.dom a) :=
  λ x, (dom_dom x) ⬝ (cod_dom x)⁻¹

  @[hott] def cod_endo : Π a, 𝒞.endo (𝒞.cod a) :=
  λ x, (dom_cod x) ⬝ (cod_cod x)⁻¹

  @[hott] def id_endo (a : 𝒞.carrier) : 𝒞.id a → 𝒞.endo a :=
  begin
    intro p, change _ = _, symmetry, transitivity,
    apply Id.map, exact p, apply cod_dom
  end

  @[hott] def following.comp_left {f g h : 𝒞.carrier} :
    𝒞.following g h → 𝒞.following (𝒞.μ f g) h :=
  begin intros p, apply Id.trans, apply mul_dom, exact p end

  @[hott] def following.comp_right {f g h : 𝒞.carrier} :
    𝒞.following f g → 𝒞.following f (𝒞.μ g h) :=
  begin intros p, apply Id.trans, exact p, exact (mul_cod g h)⁻¹ end

  @[hott] def id_iff_eq_cod (a : 𝒞.carrier) : 𝒞.id a ↔ (a = 𝒞.cod a) :=
  begin
    split, { intro p, transitivity, exact p, apply id_endo a p },
    { intro p, change _ = _, transitivity, exact p, symmetry,
      transitivity, apply Id.map, exact p, apply dom_cod }
  end

  @[hott] instance dual : category 𝒞ᵒᵖ :=
  begin
    split; repeat { intro }, apply bottom_right, apply bottom_left,
    apply bottom_cod, apply bottom_dom, apply cod_comp, apply dom_comp,
    apply mul_cod, apply mul_dom, apply cod_dom, apply dom_cod,
    symmetry, apply mul_assoc, change 𝒞.carrier at a, change 𝒞.carrier at b,
    transitivity, apply mul_def b a, assumption, assumption, split; apply Id.inv
  end

  /-
    https://ncatlab.org/nlab/show/natural+transformation
    “In terms of morphismwise components”

    “Categories for the Working Mathematician”
    I. 4. Natural Transformations. Exercise 5.
  -/
  @[hott] def natural {𝒜 ℬ : precategory} (F G : 𝒜 ⤳ ℬ) :=
  Σ (μ : 𝒜.carrier → ℬ.carrier), Π f g, 𝒜.following f g →
    ℬ.μ (μ f) (F.ap g) = ℬ.μ (G.ap f) (μ g)

  infix ` ⟹ `:25 := natural

  @[hott, refl] def id {𝒜 ℬ : precategory} {F : 𝒜 ⤳ ℬ} : F ⟹ F :=
  ⟨F.ap, λ _ _ _, Id.refl⟩

  @[hott] def natural.happly {𝒜 ℬ : precategory} {F G : 𝒜 ⤳ ℬ}
    {μ η : F ⟹ G} (p : μ = η) : μ.fst ~ η.fst :=
  begin induction p, reflexivity end

  @[hott] def natural.funext {𝒜 ℬ : precategory} {F G : 𝒜 ⤳ ℬ}
    {μ η : F ⟹ G} (p : μ.fst ~ η.fst) : μ = η :=
  begin
    fapply sigma.prod, apply theorems.funext, exact p,
    repeat { apply structures.pi_prop, intro }, apply ℬ.hset
  end
end category

end ground_zero.algebra