import ground_zero.HITs.pushout ground_zero.HITs.interval
import ground_zero.types.integer ground_zero.types.swale
open ground_zero.types

/-
  Homotopical reals R.
  * HoTT 8.1.5
-/

namespace ground_zero.HITs
universes u v w

hott theory

local notation ℤ := integer

inductive reals.rel : ℤ → ℤ → Type
| glue (x : ℤ) : reals.rel x (integer.succ x)
def reals := graph reals.rel
notation `R` := reals

namespace reals
  def elem : ℤ → R := graph.elem
  def glue (z : ℤ) : elem z = elem (integer.succ z) :> R :=
  graph.line (rel.glue z)

  def ind {π : R → Sort u} (cz : Π x, π (elem x))
    (sz : Π z, cz z =[glue z] cz (integer.succ z))
    (u : R) : π u := begin
    fapply graph.ind, exact cz,
    { intros u v H, cases H, apply sz }
  end

  def rec {π : Sort u} (cz : ℤ → π)
    (sz : Π z, cz z = cz (integer.succ z) :> π) : R → π :=
  ind cz (λ x, dep_path.pathover_of_eq (glue x) (sz x))

  def positive : Π n, elem 0 = elem (integer.pos n) :> R
  | 0 := ground_zero.types.eq.refl (elem 0)
  | (n + 1) := positive n ⬝ glue (integer.pos n)

  def negative : Π n, elem 0 = elem (integer.neg n) :> R
  | 0 := (glue (integer.neg 0))⁻¹
  | (n + 1) := negative n ⬝ (glue $ integer.neg (n + 1))⁻¹

  def center : Π z, elem 0 = elem z :> R
  | (integer.pos n) := positive n
  | (integer.neg n) := negative n

  def vect (u v : ℤ) : elem u = elem v :> R :=
  (center u)⁻¹ ⬝ center v

  def contr : ground_zero.structures.contr R :=
  { point := elem 0,
    intro := @ind (λ x, elem 0 = x :> R) center (begin
      intro z, apply equiv.path_over_subst,
      transitivity, apply equiv.transport_composition,
      induction z,
      { trivial },
      { induction z with z ih,
        { apply eq.inv_comp },
        { transitivity, symmetry, apply eq.assoc,
          transitivity, apply eq.map, apply eq.inv_comp,
          transitivity, apply eq.refl_right,
          reflexivity } }
    end) }

  def dist : Π (u v : R), u = v :> R :=
  ground_zero.structures.contr_impl_prop contr

  def lift (f : ℤ → ℤ) : R → R :=
  rec (elem ∘ f) (begin intros, apply dist end)

  def operator (f : ℤ → ℤ → ℤ) : R → R → R :=
  rec (λ x, rec (elem ∘ f x) (begin intros, apply dist end)) (begin
    intros, apply interval.funext, intro x, apply dist
  end)

  instance : has_neg R := ⟨lift integer.negate⟩

  instance : has_add R := ⟨operator integer.add⟩
  instance : has_sub R := ⟨operator integer.sub⟩
  instance : has_mul R := ⟨operator integer.mul⟩

  instance : has_coe integer R := ⟨elem⟩

  instance : has_zero R := ⟨elem 0⟩
  instance : has_one R := ⟨elem 1⟩
end reals

def complex := R × R
notation `C` := complex

namespace complex
  def inj (x : R) : C := ⟨x, 0⟩

  def add : C → C → C
  | ⟨a, b⟩ ⟨c, d⟩ := ⟨a + c, b + d⟩
  instance : has_add C := ⟨add⟩

  def mul : C → C → C
  | ⟨a, b⟩ ⟨c, d⟩ := ⟨a * c - b * d, a * d + b * c⟩
  instance : has_mul C := ⟨mul⟩

  def neg : C → C
  | ⟨a, b⟩ := ⟨-a, -b⟩
  instance : has_neg C := ⟨neg⟩

  instance : has_coe R C := ⟨inj⟩
  instance : has_zero C := ⟨inj 0⟩
  instance : has_one C := ⟨inj 1⟩

  def i : C := ⟨0, 1⟩
  example : i * i = -1 := by trivial

  def conj : C → C
  | ⟨a, b⟩ := ⟨a, -b⟩

  abbreviation Re : C → R := product.pr₁
  abbreviation Im : C → R := product.pr₂
end complex

namespace geometry
  notation `R²` := R × R

  class is_euclidian (S : Sort u) :=
  (B : S → S → S → Sort u)
  (equ : S → S → Sort u)
  (cong : S × S → S × S → Sort u)
  -- Tarski axioms
  (cong_refl (x y : S) : cong ⟨x, y⟩ ⟨y, x⟩)
  (cong_trans (a b c : S × S) : cong a b → cong a c → cong b c)
  (identity_of_congruence (x y z : S) : cong ⟨x, y⟩ ⟨z, z⟩ → equ x y)
  (segment_construction (x y a b : S) : Σ' z,
    B x y z × cong ⟨y, z⟩ ⟨a, b⟩)
  (five_segment (x y z x' y' z' u u' : S) :
    ¬(equ x y) →
    B x y z → B x' y' z' →
    cong ⟨x, y⟩ ⟨x', y'⟩ →
    cong ⟨y, z⟩ ⟨y', z'⟩ →
    cong ⟨x, u⟩ ⟨x', u'⟩ →
    cong ⟨y, u⟩ ⟨y', u'⟩ →
    cong ⟨z, u⟩ ⟨z', u'⟩)
  (identity_of_betweenness (x y : S) : B x y x → equ x y)
  (axiom_of_Pasch (x y z u v : S) :
    B x y z → B y v z → Σ' a, B u a y × B v a x)
  (lower_dimension (a b c : S) :
    ¬(B a b c) × ¬(B b c a) × ¬(B c a b))
  (upper_dimension (x y z u v : S) :
    cong ⟨x, u⟩ ⟨x, v⟩ →
    cong ⟨y, u⟩ ⟨y, v⟩ →
    cong ⟨z, u⟩ ⟨z, v⟩ →
    ¬(equ u v) →
    B x y z × B y z x × B z x y)
  (axiom_of_Euclid (x y z u v : S) :
    B x u v → B y u z → ¬(equ x y) →
    Σ' a b, B x y a × B x z b × B a v b)
  (axiom_schema_of_Continuity (φ ψ : S → Sort u) :
    (Σ' a, ∀ x y, φ x → ψ y → B a x y) →
    (Σ' b, ∀ x y, φ x → ψ y → B x b y))
  open is_euclidian

  notation a ` ≅ ` b := is_euclidian.cong a b

  section
    variables {S : Sort u} [is_euclidian S]

    notation `{` binder ` | ` r:(scoped P, swale.mk P) `}` := r

    instance in_segment : has_mem S (S × S) :=
    ⟨λ x a, B a.pr₁ x a.pr₂⟩

    def line (x y : S) :=
    { z | B y x z + B x y z + B x z y }

    def circle (radius : S × S) :=
    { z | ⟨radius.pr₁, z⟩ ≅ radius }

    def disk (radius : S × S) : swale S :=
    { z | Σ' (a : S × S), equ a.pr₁ radius.pr₁ × (a ≅ radius) × z ∈ a }

    def triangle (a b c : S) :=
    { z | B a z c + B a z b + B b z c }

    def ray (a b : S) :=
    { c | B a c b + B a b c }

    def angle (a b c : S) : swale S :=
    { z | (z ∈ ray b a) + (z ∈ ray b c) }

    def parallel (a b : swale S) :=
    ¬(Σ' (z : S), z ∈ a × z ∈ b)

    def segment.is_sum (r₁ r₂ r : S × S) :=
    Σ' z, (⟨r.pr₁, z⟩ ≅ r₁) × (⟨r.pr₂, z⟩ ≅ r₂)

    def sigma_unique (p : S → Sort v) :=
    Σ' x, p x × (Π y, p y → equ y x)

    notation `Σ!` binders `, ` r:(scoped P, sigma_unique P) := r

    def tang (A₁ A₂ : swale S) :=
    Σ! (z : S), z ∈ A₁ × z ∈ A₂

    def circle.tang (r₁ r₂ : S × S) :=
    tang (circle r₁) (circle r₂)

    theorem sum_of_radiuses_tang_circles (r₁ r₂ : S × S)
      (h : circle.tang r₁ r₂) :
      segment.is_sum r₁ r₂ ⟨r₁.pr₁, r₂.pr₁⟩ := begin
      cases h with z cond,
      cases cond with cond trash, clear trash,
      cases cond with belongs₁ belongs₂,
      existsi z, split,
      exact belongs₁, exact belongs₂
    end
  end
end geometry

end ground_zero.HITs