namespace ground_zero.theorems.geometry

universe u

class is_euclidian (S : Type u) :=
(B : S → S → S → Prop)
(cong : S × S → S × S → Prop)
-- Tarski axioms
(cong_refl (x y : S) : cong ⟨x, y⟩ ⟨y, x⟩)
(cong_trans (a b c : S × S) : cong a b → cong a c → cong b c)
(identity_of_congruence (x y z : S) : cong ⟨x, y⟩ ⟨z, z⟩ → x = y)
(segment_construction (x y a b : S) :
  ∃ z, B x y z ∧ cong ⟨y, z⟩ ⟨a, b⟩)
(five_segment (x y z x' y' z' u u' : S) :
  x ≠ y →
  B x y z → B x' y' z' →
  cong ⟨x, y⟩ ⟨x', y'⟩ →
  cong ⟨y, z⟩ ⟨y', z'⟩ →
  cong ⟨x, u⟩ ⟨x', u'⟩ →
  cong ⟨y, u⟩ ⟨y', u'⟩ →
  cong ⟨z, u⟩ ⟨z', u'⟩)
(identity_of_betweenness (x y : S) : B x y x → x = y)
(axiom_of_Pasch (x y z u v : S) :
  B x y z → B y v z → ∃ a, B u a y ∧ B v a x)
(lower_dimension (a b c : S) :
  ¬B a b c ∧ ¬B b c a ∧ ¬B c a b)
(upper_dimension (x y z u v : S) :
  cong ⟨x, u⟩ ⟨x, v⟩ →
  cong ⟨y, u⟩ ⟨y, v⟩ →
  cong ⟨z, u⟩ ⟨z, v⟩ →
  u ≠ v →
  B x y z ∧ B y z x ∧ B z x y)
(axiom_of_Euclid (x y z u v : S) :
  B x u v → B y u z → x ≠ y →
  ∃ a b, B x y a ∧ B x z b ∧ B a v b)
(axiom_schema_of_Continuity (φ ψ : S → Prop) :
  (Σ' a, ∀ x y, φ x → ψ y → B a x y) →
  (Σ' b, ∀ x y, φ x → ψ y → B x b y))
open is_euclidian

notation a ` ≅ ` b := is_euclidian.cong a b

section
  variables {S : Type u} [is_euclidian S]

  instance : has_mem S (S × S) :=
  ⟨λ x a, B a.fst x a.snd⟩

  def segment (x y : S) :=
  { z | B x z y }

  def line (x y : S) :=
  { z | B y x z ∨ B x y z ∨ B x z y }

  def circle (radius : S × S) :=
  { z | ⟨radius.fst, z⟩ ≅ radius }

  def disk (radius : S × S) : set S :=
  { z | ∃ (a : S × S), a.fst = radius.fst ∧ (a ≅ radius) ∧ z ∈ a }

  def triangle (a b c : S) :=
  { z | B a z c ∨ B a z b ∨ B b z c }

  def ray (a b : S) :=
  { c | B a c b ∨ B a b c }

  def angle (a b c : S) : set S :=
  { z | z ∈ ray b a ∨ z ∈ ray b c }

  def parallel (a b : set S) :=
  ¬∃ (z : S), (z ∈ a) ∧ z ∈ b

  def segment.is_sum (r₁ r₂ r : S × S) :=
  ∃ z, ((r.fst, z) ≅ r₁) ∧ ((r.snd, z) ≅ r₂) ∧ B r.fst z r.snd

  def circle.touch_externally (r₁ r₂ : S × S) :=
  ∃! (z : S), z ∈ circle r₁ ∧ z ∈ circle r₂ ∧ B r₁.fst z r₂.fst

  theorem sum_of_radiuses_tang_circles
    (r₁ r₂ : S × S) (h : circle.touch_externally r₁ r₂) :
    segment.is_sum r₁ r₂ (r₁.fst, r₂.fst) := begin
    cases h with z cond,
    cases cond with cond trash, clear trash,
    cases cond with belongs₁ cond,
    cases cond with belongs₂ H,
    existsi z, repeat { try { split }, assumption }
  end
end

end ground_zero.theorems.geometry