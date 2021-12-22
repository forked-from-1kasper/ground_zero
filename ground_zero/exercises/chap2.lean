import ground_zero.theorems.prop
import ground_zero.structures

open ground_zero ground_zero.types
open ground_zero.types.equiv
open ground_zero.proto

open ground_zero.structures (prop contr)

universes u v u' v' w w' k k'
hott theory

-- exercise 2.1

section
  variables {α : Type u} {a b c : α}

  @[hott] def trans₁ (p : a = b) (q : b = c) : a = c :=
  @Id.rec α a (λ x _, x = c → a = c) (@Id.rec α a (λ x _, a = x) (idp a) c) b p q

  infixl ` ⬝₁ `:99 := trans₁

  @[hott] def trans₂ (p : a = b) (q : b = c) : a = c :=
  @Id.rec α a (λ x _, x = c → a = c) idfun b p q

  infixl ` ⬝₂ `:99 := trans₂

  @[hott] def trans₃ (p : a = b) (q : b = c) : a = c :=
  @Id.rec α b (λ x _, a = b → a = x) idfun c q p

  infixl ` ⬝₃ `:99 := trans₃

  @[hott] def eq₁₂ (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₂ q :=
  begin induction p, induction q, reflexivity end

  @[hott] def eq₂₃ (p : a = b) (q : b = c) : p ⬝₂ q = p ⬝₃ q :=
  begin induction p, induction q, reflexivity end

  @[hott] def eq₁₃ (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₃ q :=
  begin induction p, induction q, reflexivity end
end

-- exercise 2.2

section
  variables {α : Type u} {a b c : α} (p : a = b) (q : b = c)

  @[hott] example : eq₁₂ p q ⬝ eq₂₃ p q = eq₁₃ p q :=
  begin induction p, induction q, reflexivity end
end

-- exercise 2.3

section
  variables {α : Type u} {a b c : α}

  @[hott] def trans₄ (p : a = b) (q : b = c) : a = c :=
  @Id.rec α b (λ x _, a = b → a = x) (@Id.rec α a (λ x _, a = x) (idp a) b) c q p

  infixl ` ⬝₄ `:99 := trans₄

  /-
  example (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₄ q := idp _
  example (p : a = b) (q : b = c) : p ⬝₂ q = p ⬝₄ q := idp _
  example (p : a = b) (q : b = c) : p ⬝₃ q = p ⬝₄ q := idp _
  -/

  @[hott] example (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₄ q :=
  begin induction p, induction q, reflexivity end
end

-- exercise 2.4

@[hott] def n_path (α : Type u) : ℕ → Type u
|    0    := α
| (n + 1) := Σ (a b : n_path n), a = b

notation n `-Path` := λ α, n_path α n

@[hott] def boundary {α : Type u} {n : ℕ} : (n + 1)-Path α → (n-Path α) × (n-Path α) :=
λ ⟨a, b, _⟩, (a, b)

-- exercise 2.5

namespace «2.5»
  variables {α : Type u} {β : Type v} {x y : α} (p : x = y)

  @[hott] def transconst (b : β) : transport (λ _, β) p b = b :=
  begin induction p, reflexivity end

  @[hott] def f (φ : α → β) :
    φ x = φ y → transport (λ _, β) p (φ x) = φ y :=
  λ q, transconst p (φ x) ⬝ q

  @[hott] def g (φ : α → β) :
    transport (λ _, β) p (φ x) = φ y → φ x = φ y :=
  λ q, (transconst p (φ x))⁻¹ ⬝ q

  @[hott] example (φ : α → β) : f p φ ∘ g p φ ~ id :=
  begin induction p, reflexivity end

  @[hott] example (φ : α → β) : g p φ ∘ f p φ ~ id :=
  begin induction p, reflexivity end
end «2.5»

-- exercise 2.6

@[hott] example {α : Type u} {x y z : α} (p : x = y) : biinv (@Id.trans α x y z p) :=
begin split; existsi (Id.trans p⁻¹); intro q; induction p; induction q; reflexivity end

-- exercise 2.7

namespace «2.7»
  variables {α : Type u} {α' : Type u'} {β : α → Type v} {β' : α' → Type v'}
            (g : α → α') (h : Π a, β a → β' (g a))

  def φ (x : Σ a, β a) : Σ a', β' a' := ⟨g x.1, h x.1 x.2⟩

  @[hott] example (x y : Σ a, β a) (p : x.1 = y.1) (q : x.2 =[p] y.2) :
      Id.map (φ g h) (sigma.prod p q)
    = @sigma.prod α' β' (φ g h x) (φ g h y)
        (@Id.map α α' x.1 y.1 g p) (dep_path_map' g h q) :=
  begin
    induction x with x u, induction y with y v,
    change x = y at p, induction p,
    change u = v at q, induction q,
    reflexivity
  end
end «2.7»

-- exercise 2.8

namespace «2.8»
  variables {α α' β β' : Type u} (g : α → α') (h : β → β')

  def φ : α + β → α' + β' :=
  coproduct.elim (coproduct.inl ∘ g) (coproduct.inr ∘ h)

  @[hott] def ρ {x y : α + β} (p : coproduct.code x y) : coproduct.code (φ g h x) (φ g h y) :=
  begin induction x; induction y; try { { apply Id.map, exact p } <|> induction p } end

  @[hott] example (x y : α + β) (p : coproduct.code x y) :
      Id.map (φ g h) (coproduct.path_sum x y p)
    = coproduct.path_sum (φ g h x) (φ g h y) (ρ g h p) :=
  begin induction x; induction y; { induction p, try { reflexivity } } end
end «2.8»

-- exercise 2.9

@[hott] def coproduct.dep_univ_property (A : Type u) (B : Type v) (X : A + B → Type w) :
  (Π x, X x) ≃ (Π a, X (coproduct.inl a)) × (Π b, X (coproduct.inr b)) :=
begin
  fapply sigma.mk, { intro φ, exact (λ a, φ (coproduct.inl a), λ b, φ (coproduct.inr b)) },
  apply qinv.to_biinv, fapply sigma.mk, { intros φ x, induction x, apply φ.1, apply φ.2 },
  split, { intro x, induction x with φ ψ,  reflexivity },
  { intro f, apply theorems.funext, intro y, induction y; reflexivity }
end

@[hott] def coproduct.univ_property (A : Type u) (B : Type v) (X : Type w) :
  (A + B → X) ≃ (A → X) × (B → X) :=
coproduct.dep_univ_property A B (λ _, X)

-- exercise 2.10

@[hott] def sigma.assoc (A : Type u) (B : A → Type v) (C : (Σ x, B x) → Type w) :
  (Σ x, Σ y, C ⟨x, y⟩) ≃ (Σ p, C p) :=
begin
  fapply sigma.mk, { intro w, existsi (⟨w.1, w.2.1⟩ : Σ x, B x), exact w.2.2 },
  apply qinv.to_biinv, fapply sigma.mk,
  { intro w, existsi w.1.1, existsi w.1.2, apply transport C,
    symmetry, exact sigma.uniq w.1, exact w.2 }, split; intro w,
  { induction w with w c, induction w with a b, reflexivity },
  { induction w with a w, induction w with b c, reflexivity }
end

-- exercise 2.11

namespace «2.11»
  variables {P : Type k} {A : Type u} {B : Type v} {C : Type w}
            (η : pullback_square P A B C)

  @[hott] example : P ≃ pullback C η.1.right η.1.bot :=
  begin
    transitivity, symmetry, apply structures.cozero_morphism_eqv,
    transitivity, fapply sigma.mk, exact η.1.induced 𝟏, apply η.2,
    transitivity, apply theorems.prop.respects_equiv_over_fst,
    apply ua.product_equiv₃; apply structures.cozero_morphism_eqv,
    apply sigma.respects_equiv, intro w,
    transitivity, apply theorems.full,
    transitivity, apply structures.family_over_unit,
    induction w with a b, reflexivity
  end
end «2.11»

-- exercise 2.12

namespace «2.12»
  variables {A : Type u} {B : Type u'}
            {C : Type v} {D : Type v'}
            {E : Type w} {F : Type w'}
            {f : A → C} {g : C → E}
            {i : A → B} {j : C → D} {k : E → F}
            {h : B → D} {s : D → F}
            (α : j ∘ f = h ∘ i :> A → D)
            (β : k ∘ g = s ∘ j :> C → F)

  include α β

  def left  : hcomm_square A C B D := ⟨j, h, f, i, α⟩
  def right : hcomm_square C E D F := ⟨k, s, g, j, β⟩

  def outer : hcomm_square A E B F :=
  ⟨k, s ∘ h, g ∘ f, i, @Id.map (C → F) (A → F) _ _ (∘ f) β
                     ⬝ @Id.map _ (A → F) _ _ (λ φ, s ∘ φ) α⟩

  -- ???
end «2.12»

-- exercise 2.13

example : (𝟐 ≃ 𝟐) ≃ 𝟐 := theorems.prop.bool_equiv_eqv_bool

-- exercise 2.15

@[hott] example {A : Type u} {B : A → Type v} {x y : A} (p : x = y) :
  transport B p = idtoeqv (B # p) :=
begin induction p, reflexivity end

-- exercise 2.18

@[hott] example {A : Type u} {B : A → Type v} {f g : Π x, B x}
  (H : f ~ g) {x y : A} (p : x = y) :
    (transport B p) # (H x) ⬝ apd g p = apd f p ⬝ H y :=
begin induction p, transitivity, apply Id.refl_right, apply equiv.idmap end
