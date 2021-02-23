import ground_zero.types.ens
open ground_zero.types ground_zero.structures
open ground_zero (vect)

hott theory

/-
  Magma, semigroup, monoid, group, abelian group.
  * HoTT 6.11
-/

namespace ground_zero.algebra
  universes u v w

  def zeroeqv {α : Type u} (H : hset α) : 0-Type :=
  ⟨α, zero_eqv_set.left (λ _ _, H)⟩

  structure magma :=
  (α : 0-Type) (φ : α.fst → α.fst → α.fst)

  def magma.zero : magma → (0-Type) := magma.α
  def magma.carrier (M : magma) := M.α.fst

  def magma.set (M : magma) : hset M.carrier :=
  λ _ _, zero_eqv_set.forward M.α.snd

  structure semigroup extends magma :=
  (mul_assoc : Π a b c, φ (φ a b) c = φ a (φ b c))

  def semigroup.carrier (S : semigroup) := S.α.fst
  def semigroup.set (S : magma) : hset S.carrier :=
  λ _ _, zero_eqv_set.forward S.α.snd

  structure monoid extends semigroup :=
  (e : α.fst) (one_mul : Π a, φ e a = a) (mul_one : Π a, φ a e = a)

  def monoid.carrier (M : monoid) := M.α.fst

  def monoid.set (M : monoid) : hset M.carrier :=
  λ _ _, zero_eqv_set.forward M.α.snd

  structure group extends monoid :=
  (inv : α.fst → α.fst) (mul_left_inv : Π a, φ (inv a) a = e)

  def group.to_magma : group → magma :=
  semigroup.to_magma ∘ monoid.to_semigroup ∘ group.to_monoid

  def group.carrier (G : group) := G.α.fst

  def group.set (G : group) : hset G.carrier :=
  λ _ _, zero_eqv_set.forward G.α.snd

  def group.subset (G : group) := ens G.carrier
  def group.univ (G : group) : G.subset := ens.univ G.carrier

  def group.zero : group → (0-Type) :=
  magma.zero ∘ group.to_magma

  class abelian (G : group) :=
  (mul_comm : Π a b, G.φ a b = G.φ b a)

  @[hott] def magma.ext (M₁ M₂ : magma) (p : M₁.carrier = M₂.carrier)
    (q : M₁.φ =[λ M, M → M → M, p] M₂.φ) : M₁ = M₂ :=
  begin
    induction M₁ with M₁ φ₁, induction M₂ with M₂ φ₂,
    induction M₁ with M₁ H₁, induction M₂ with M₂ H₂,
    change M₁ = M₂ at p, induction p,
    have r := ntype_is_prop 0 H₁ H₂,
    induction r, apply Id.map, apply q
  end

  @[hott] def semigroup.ext (S₁ S₂ : semigroup) (p : S₁.carrier = S₂.carrier)
    (q : S₁.φ =[λ M, M → M → M, p] S₂.φ) : S₁ = S₂ :=
  begin
    induction S₁ with S₁ p₁, induction S₂ with S₂ p₂,
    have p := magma.ext S₁ S₂ p q, induction p, apply Id.map,
    repeat { apply pi_prop, intro }, apply S₁.set
  end

  meta def propauto :=
  `[ repeat { apply pi_prop, intro }, apply p ]

  @[hott] def group.ext (G₁ G₂ : group) (p : G₁.carrier = G₂.carrier)
    (q : G₁.φ =[λ G, G → G → G, p] G₂.φ) (r : G₁.e =[λ G, G, p] G₂.e)
    (s : G₁.inv =[λ G, G → G, p] G₂.inv) : G₁ = G₂ :=
  begin
    induction G₁ with G₁ ι₁ r₁, induction G₂ with G₂ ι₂ r₂,
    induction G₁ with G₁ e₁ q₁ s₁, induction G₂ with G₂ e₂ q₂ s₂,
    induction G₁ with G₁ p₁, induction G₂ with G₂ p₂,
    induction G₁ with G₁ φ₁, induction G₂ with G₂ φ₂,
    induction G₁ with G₁ H₁, induction G₂ with G₂ H₂,
    change G₁ = G₂ at p, induction p,
    have h : H₁ = H₂ := ntype_is_prop 0 H₁ H₂, induction h,
    change φ₁ = φ₂ at q, induction q,
    have p : hset G₁ := λ _ _, zero_eqv_set.forward H₁,
    have α₁ : p₁ = p₂ := by propauto, induction α₁,
    change e₁ = e₂ at r, induction r,
    have α₂ : q₁ = q₂ := by propauto, induction α₂,
    have α₃ : s₁ = s₂ := by propauto, induction α₃,
    change ι₁ = ι₂ at s, induction s,
    have α₄ : r₁ = r₂ := by propauto, induction α₄,
    reflexivity
  end

  def algop (deg : ℕ) (α : Type u) :=
  vect α deg → α

  section
    variables {ι : Type u} {υ : Type v} (deg : ι + υ → ℕ)

    def algebra (α : Type w) :=
    (Π i, algop (deg (sum.inl i)) α) ×            -- algebraic operations
    (Π i, vect α (deg (sum.inr i)) → propset.{w}) -- relations

    def Alg := Σ (α : 0-Type), algebra deg α.fst
  end

  section
    variables {ι : Type u} {υ : Type v} {deg : ι + υ → ℕ}

    section
      variable (A : Alg deg)
      def Alg.carrier := A.fst.fst
      def Alg.op      := A.snd.fst
      def Alg.rel     := A.snd.snd
    end

    def homo (μ : Alg deg) (η : Alg deg) (f : μ.carrier → η.carrier) :=
    (Π i v, f (μ.op i v) = η.op i (v.map f)) ×
    (Π i v, μ.rel i v = η.rel i (v.map f))
  end

end ground_zero.algebra