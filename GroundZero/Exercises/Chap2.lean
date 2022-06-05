import GroundZero.Theorems.Prop

open GroundZero GroundZero.Types
open GroundZero.Types.Equiv
open GroundZero.Proto

open GroundZero.Structures (prop contr)

universe u v u' v' w w' k k'

-- exercise 2.1

section
  variable {α : Type u} {a b c : α}

  hott def trans₁ (p : a = b) (q : b = c) : a = c :=
  @Id.casesOn α a (λ x _, x = c → a = c) b p (@Id.casesOn α a (λ x _, a = x) c · (idp a)) q

  infixl:99 " ⬝₁ " => trans₁

  hott def trans₂ (p : a = b) (q : b = c) : a = c :=
  @Id.casesOn α a (λ x _, x = c → a = c) b p idfun q

  infixl:99 " ⬝₂ " => trans₂

  hott def trans₃ (p : a = b) (q : b = c) : a = c :=
  @Id.casesOn α b (λ x _, a = b → a = x) c q idfun p

  infixl:99 " ⬝₃ " => trans₃

  hott def eq₁₂ (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₂ q :=
  begin induction p; induction q; reflexivity end

  hott def eq₂₃ (p : a = b) (q : b = c) : p ⬝₂ q = p ⬝₃ q :=
  begin induction p; induction q; reflexivity end

  hott def eq₁₃ (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₃ q :=
  begin induction p; induction q; reflexivity end
end

-- exercise 2.2

section
  variable {α : Type u} {a b c : α} (p : a = b) (q : b = c)

  example : eq₁₂ p q ⬝ eq₂₃ p q = eq₁₃ p q :=
  begin induction p; induction q; reflexivity end
end

-- exercise 2.3

section
  variable {α : Type u} {a b c : α}

  hott def trans₄ (p : a = b) (q : b = c) : a = c :=
  @Id.casesOn α b (λ x _, a = b → a = x) c q (@Id.casesOn α a (λ x _, a = x) b · (idp a)) p

  infixl:99 " ⬝₄ " => trans₄

  /-
  example (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₄ q := idp _
  example (p : a = b) (q : b = c) : p ⬝₂ q = p ⬝₄ q := idp _
  example (p : a = b) (q : b = c) : p ⬝₃ q = p ⬝₄ q := idp _
  -/

  example (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₄ q :=
  begin induction p; induction q; reflexivity end
end

-- exercise 2.4

hott def nPath (α : Type u) : ℕ → Type u
| Nat.zero   => α
| Nat.succ n => Σ (a b : nPath α n), a = b

hott def boundary {α : Type u} {n : ℕ} :
  nPath α (n + 1) → (nPath α n) × (nPath α n) :=
λ ⟨a, b, _⟩, (a, b)

-- exercise 2.5

namespace «2.5»
  variable {α : Type u} {β : Type v} {x y : α} (p : x = y)

  hott def transconst (b : β) : transport (λ _, β) p b = b :=
  begin induction p; reflexivity end

  hott def f (φ : α → β) : φ x = φ y → transport (λ _, β) p (φ x) = φ y :=
  λ q, transconst p (φ x) ⬝ q

  hott def g (φ : α → β) : transport (λ _, β) p (φ x) = φ y → φ x = φ y :=
  λ q, (transconst p (φ x))⁻¹ ⬝ q

  example (φ : α → β) : f p φ ∘ g p φ ~ id :=
  begin induction p; reflexivity end

  example (φ : α → β) : g p φ ∘ f p φ ~ id :=
  begin induction p; reflexivity end
end «2.5»

-- exercise 2.6

example {α : Type u} {x y z : α} (p : x = y) : biinv (@Id.trans α x y z p) :=
begin apply Prod.mk <;> existsi Id.trans p⁻¹ <;> intro q <;> induction p <;> induction q <;> reflexivity end

-- exercise 2.7

namespace «2.7»
  variable {α : Type u} {α' : Type u'} {β : α → Type v} {β' : α' → Type v'}
           (g : α → α') (h : Π a, β a → β' (g a))

  def φ (x : Σ a, β a) : Σ a', β' a' := ⟨g x.1, h x.1 x.2⟩

  hott def prodMap : Π (x y : Σ a, β a) (p : x.1 = y.1) (q : x.2 =[p] y.2),
      Id.map (φ g h) (Sigma.prod p q)
    = @Sigma.prod α' β' (φ g h x) (φ g h y)
        (@Id.map α α' x.1 y.1 g p) (depPathMap' g h q) :=
  begin
    intro ⟨x, H⟩ ⟨y, G⟩ (p : x = y); induction p;
    intro (q : H = G); induction q; reflexivity
  end
end «2.7»

-- exercise 2.8

namespace «2.8»
  variable {α α' β β' : Type u} (g : α → α') (h : β → β')

  def φ : α + β → α' + β' :=
  Coproduct.elim (Coproduct.inl ∘ g) (Coproduct.inr ∘ h)

  hott def ρ : Π {x y : α + β} (p : Coproduct.code x y), Coproduct.code (φ g h x) (φ g h y)
  | Sum.inl _, Sum.inl _, p => Id.map _ p
  | Sum.inr _, Sum.inl _, p => Empty.elim p
  | Sum.inl _, Sum.inr _, p => Empty.elim p
  | Sum.inr _, Sum.inr _, p => Id.map _ p

  hott def mapPathSum (x y : α + β) : Π p,
      Id.map (φ g h) (Coproduct.pathSum x y p)
    = Coproduct.pathSum (φ g h x) (φ g h y) (ρ g h p) :=
  begin
    match x, y with
    | Sum.inl x, Sum.inl y => _
    | Sum.inr _, Sum.inl _ => _
    | Sum.inl _, Sum.inr _ => _
    | Sum.inr x, Sum.inr y => _;

    { intro (p : x = y); induction p; reflexivity };
    { intro; apply Empty.elim; assumption };
    { intro; apply Empty.elim; assumption };
    { intro (p : x = y); induction p; reflexivity }
  end
end «2.8»

-- exercise 2.9

hott def Coproduct.depUnivProperty (A : Type u) (B : Type v) (X : A + B → Type w) :
  (Π x, X x) ≃ (Π a, X (Coproduct.inl a)) × (Π b, X (Coproduct.inr b)) :=
begin
  fapply Sigma.mk; { intro φ; exact (λ a, φ (Coproduct.inl a), λ b, φ (Coproduct.inr b)) };
  apply Qinv.toBiinv; fapply Sigma.mk;
  { intros φ x; induction x using Sum.casesOn; apply φ.1; apply φ.2 };
  apply Prod.mk; { intro (φ, ψ); reflexivity };
  { intro f; apply Theorems.funext; intro z; induction z using Sum.casesOn <;> reflexivity }
end

hott def Coproduct.univProperty (A : Type u) (B : Type v) (X : Type w) :
  (A + B → X) ≃ (A → X) × (B → X) :=
Coproduct.depUnivProperty A B (λ _, X)

-- exercise 2.10

hott def sigma.assoc (A : Type u) (B : A → Type v) (C : (Σ x, B x) → Type w) :
  (Σ x, Σ y, C ⟨x, y⟩) ≃ (Σ p, C p) :=
begin
  fapply Sigma.mk; { intro w; existsi ⟨w.1, w.2.1⟩; exact w.2.2 };
  apply Qinv.toBiinv; fapply Sigma.mk;
  { intro w; existsi w.1.1; existsi w.1.2; apply transport C;
    symmetry; exact Sigma.uniq w.1; exact w.2 }; apply Prod.mk;
  { intro ⟨⟨a, b⟩, c⟩; reflexivity };
  { intro ⟨a, ⟨b, c⟩⟩; reflexivity }
end

-- exercise 2.11

namespace «2.11»
  variable {P : Type k} {A : Type u} {B : Type v} {C : Type w}
           (η : pullbackSquare P A B C)

  hott def pullbackCorner : P ≃ pullback C η.1.right η.1.bot :=
  begin
    apply Equiv.trans; apply Equiv.symm; apply Structures.cozeroMorphismEqv;
    apply Equiv.trans; fapply Sigma.mk; exact η.1.induced 𝟏; apply η.2;
    apply Equiv.trans; apply Theorems.Prop.respectsEquivOverFst;
    apply ua.productEquiv₃ <;> apply Structures.cozeroMorphismEqv;
    apply Sigma.respectsEquiv; intro ⟨a, b⟩;
    apply Equiv.trans; apply Theorems.full;
    apply Structures.familyOverUnit
  end
end «2.11»

-- exercise 2.12

namespace «2.12»
  variable {A : Type u} {B : Type u'}
           {C : Type v} {D : Type v'}
           {E : Type w} {F : Type w'}
           {f : A → C} {g : C → E}
           {i : A → B} {j : C → D} {k : E → F}
           {h : B → D} {s : D → F}
           (α : j ∘ f = h ∘ i)
           (β : k ∘ g = s ∘ j)

  def left  : hcommSquare A C B D := ⟨j, h, f, i, α⟩
  def right : hcommSquare C E D F := ⟨k, s, g, j, β⟩

  def outer : hcommSquare A E B F :=
  ⟨k, s ∘ h, g ∘ f, i, @Id.map (C → F) (A → F) _ _ (· ∘ f) β
                     ⬝ @Id.map _ (A → F) _ _ (s ∘ ·) α⟩

  hott def pullbackLemma (H : (right α).isPullback) :
    (left β).isPullback ↔ (outer α β).isPullback :=
  sorry
end «2.12»

-- exercise 2.13

example : (𝟐 ≃ 𝟐) ≃ 𝟐 := Theorems.Prop.boolEquivEqvBool

-- exercise 2.14

-- Assume Γ, p : x = y ⊢ x ≡ y, let Γ = A : U, a : A. Then Γ, b : A, p : a = b ⊢ p = idp a : U,
-- because in this context we have p : a = b, so a ≡ b, so p : a = a.
-- “@Id.rec A a (λ b, p = idp a) (λ x, idp a) a” is then well-typed.
-- This means that we have a proof of “Π (p : a = a) → p = idp a” leading to contradiction.

-- exercise 2.15

hott def transportMap {A : Type u} {B : A → Type v} {x y : A} (p : x = y) :
  transport B p = idtoeqv (Id.map B p) :=
begin induction p; reflexivity end

-- exercise 2.18

hott def transportSquare {A : Type u} {B : A → Type v} {f g : Π x, B x} (H : f ~ g) {x y : A} (p : x = y) :
  Id.map (transport B p) (H x) ⬝ apd g p = apd f p ⬝ H y :=
begin induction p; transitivity; apply Id.reflRight; apply Equiv.idmap end