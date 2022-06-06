import GroundZero.Meta.Basic

namespace GroundZero.Proto
universe u v w

hott def idfun {A : Sort u} : A → A :=
(a ↦ a)

inductive Empty : Type u

attribute [eliminator] Empty.casesOn

def Iff (A : Type u) (B : Type v) :=
(A → B) × (B → A)

infix:30 (priority := high) " ↔ " => Iff

hott def Iff.left  {A : Type u} {B : Type v} (w : A ↔ B) : A → B := w.1
hott def Iff.right {A : Type u} {B : Type v} (w : A ↔ B) : B → A := w.2

hott def Iff.refl {A : Type u} : A ↔ A :=
⟨idfun, idfun⟩

hott def Iff.symm {A : Type u} {B : Type v} : (A ↔ B) → (B ↔ A) :=
λ p, ⟨p.right, p.left⟩

hott def Iff.comp {A : Type u} {B : Type v} {C : Type w} :
  (A ↔ B) → (B ↔ C) → (A ↔ C) :=
λ p q, ⟨q.left ∘ p.left, p.right ∘ q.right⟩

instance : @Reflexive  (Type u) Iff := ⟨@Iff.refl⟩
instance : @Symmetric  (Type u) Iff := ⟨@Iff.symm⟩
instance : @Transitive (Type u) Iff := ⟨@Iff.comp⟩

notation "𝟎" => Empty
notation "𝟐" => Bool
notation "ℕ" => Nat

def Empty.elim {A : Sort u} (xs : Empty) : A :=
nomatch xs

def Bool.elim {A : Sort u} : A → A → 𝟐 → A :=
λ b₁ b₂ b, @Bool.casesOn (λ _, A) b b₁ b₂

def Bottom := Empty.{0}
notation (priority := low) "⊥" => Bottom

inductive Identity (A : Type u)
| elem : A → Identity A

attribute [eliminator] Identity.casesOn

def Identity.elim {A : Type u} : Identity A → A
| Identity.elem a => a

def Identity.lift {A : Type u} {B : Type v}
  (f : A → B) : Identity A → Identity B
| Identity.elem a => Identity.elem (f a)

def Identity.lift₂ {A : Type u} {B : Type v} {C : Type w}
  (f : A → B → C) : Identity A → Identity B → Identity C
| Identity.elem a, Identity.elem b => Identity.elem (f a b)

end GroundZero.Proto
