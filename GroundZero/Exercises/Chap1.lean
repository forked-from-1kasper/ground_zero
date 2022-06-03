import GroundZero.Types.Product
import GroundZero.Theorems.Nat
import GroundZero.Types.Sigma

open GroundZero GroundZero.Types
open GroundZero.Types.Equiv
open GroundZero.Proto

open GroundZero.Structures (prop contr)

universe u v w k

-- exercise 1.1
hott def compAssoc {α : Type u} {β : Type v} {γ : Type w} {δ : Type k}
  (f : α → β) (g : β → γ) (h : γ → δ) : h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
by reflexivity

-- exercise 1.2

hott def Product.rec' {α : Type u} {β : Type v} {γ : Type w}
  (φ : α → β → γ) : α × β → γ :=
λ u, φ u.1 u.2

example {α : Type u} {β : Type v} {γ : Type w}
  (φ : α → β → γ) (a : α) (b : β) :
  Product.rec' φ (a, b) = φ a b :=
by reflexivity

hott def Sigma.rec' {α : Type u} {β : α → Type v} {γ : Type w}
  (φ : Π x, β x → γ) : (Σ x, β x) → γ :=
λ u, φ u.1 u.2

example {α : Type u} {β : α → Type v} {γ : Type w}
  (φ : Π x, β x → γ) (a : α) (b : β a) :
  Sigma.rec' φ ⟨a, b⟩ = φ a b :=
by reflexivity

-- exercise 1.3

hott def Product.ind' {α : Type u} {β : Type v} {π : α × β → Type w}
  (φ : Π a b, π (a, b)) : Π x, π x :=
λ u, transport π (Product.uniq u) (φ u.1 u.2)

example {α : Type u} {β : Type v} {π : α × β → Type w}
  (φ : Π a b, π (a, b)) (a : α) (b : β) : Product.ind' φ (a, b) = φ a b :=
by reflexivity

hott def Sigma.ind' {α : Type u} {β : α → Type v} {π : (Σ x, β x) → Type w}
  (φ : Π a b, π ⟨a, b⟩) : Π x, π x :=
λ u, transport π (Sigma.uniq u) (φ u.1 u.2)

example {α : Type u} {β : α → Type v} {π : (Σ x, β x) → Type w}
  (φ : Π a b, π ⟨a, b⟩) (a : α) (b : β a) : Sigma.ind' φ ⟨a, b⟩ = φ a b :=
by reflexivity

-- exercise 1.4

hott def Nat.iter {C : Type u} (c₀ : C) (cₛ : C → C) : ℕ → C
| Nat.zero   => c₀
| Nat.succ n => cₛ (iter c₀ cₛ n)

hott def grec {C : Type u} (c₀ : C) (cₛ : ℕ → C → C) : ℕ → ℕ × C :=
@Nat.iter (ℕ × C) (0, c₀) (λ u, (u.1 + 1, cₛ u.1 u.2))

hott def grec.stable {C : Type u} (c₀ : C) (cₛ : ℕ → C → C) :
  Π n, (grec c₀ cₛ n).1 = n
| Nat.zero   => idp 0
| Nat.succ n => Id.map Nat.succ (stable c₀ cₛ n)

section
  variable {C : Type u} (c₀ : C) (cₛ : ℕ → C → C)

  hott def Nat.rec' : ℕ → C := Prod.pr₂ ∘ grec c₀ cₛ

  hott def Nat.iterβ₁ : Nat.rec' c₀ cₛ 0 = c₀ :=
  by reflexivity

  hott def Nat.iterβ₂ (n : ℕ) : Nat.rec' c₀ cₛ (n + 1) = cₛ n (Nat.rec' c₀ cₛ n) :=
  Id.map (λ m, cₛ m (Nat.rec' c₀ cₛ n)) (grec.stable c₀ cₛ n)
end

-- exercise 1.5

hott def Coproduct' (α β : Type u) :=
Σ (x : 𝟐), Bool.elim α β x

namespace Coproduct'
  variable {α β : Type u}

  def inl {α β : Type u} (a : α) : Coproduct' α β := ⟨false, a⟩
  def inr {α β : Type u} (b : β) : Coproduct' α β := ⟨true,  b⟩

  variable (π : Coproduct' α β → Type v) (u : Π a, π (inl a)) (v : Π b, π (inr b))

  hott def ind : Π x, π x
  | ⟨false, a⟩ => u a | ⟨true, b⟩ => v b

  hott def indβ₁ (a : α) : ind π u v (inl a) = u a :=
  by reflexivity

  hott def indβ₂ (b : β) : ind π u v (inr b) = v b :=
  by reflexivity
end Coproduct'

-- exercise 1.6

hott def Product' (α β : Type u) :=
Π (x : 𝟐), Bool.elim α β x

namespace Product'
  variable {α β : Type u}

  def mk (a : α) (b : β) : Product' α β :=
  (@Bool.casesOn (Bool.elim α β) · a b)

  def pr₁ : Product' α β → α := λ u, u false
  def pr₂ : Product' α β → β := λ u, u true

  def η (x : Product' α β) : mk (pr₁ x) (pr₂ x) = x :=
  begin apply Theorems.funext; intro b; induction b using Bool.casesOn <;> reflexivity end

  variable (π : Product' α β → Type v) (φ : Π a b, π (mk a b))

  hott def ind : Π x, π x :=
  λ x, transport π (η x) (φ (pr₁ x) (pr₂ x))

  hott def indβ (a : α) (b : β) : ind π φ (mk a b) = φ a b :=
  begin
    transitivity; apply Id.map (transport π · (φ a b));
    transitivity; apply Id.map Theorems.funext; change _ = (λ x, idp (mk a b x));
    apply Theorems.funext; intro b; induction b using Bool.casesOn <;> reflexivity;
    apply Theorems.funextId; reflexivity
  end
end Product'

-- exercise 1.7

hott def Ind :=
Π (A : Type u) (C : Π x y, x = y → Type v),
  (Π x, C x x (idp x)) → Π (x y : A) (p : x = y), C x y p

hott def Ind' :=
Π (A : Type u) (a : A) (C : Π x, a = x → Type v),
  C a (idp a) → Π (x : A) (p : a = x), C x p

-- note that φ involves “max u (v + 1)”
example (φ : Ind.{u, max u (v + 1)}) : Ind'.{u, v} :=
λ A a C c x p, φ A (λ x y p, Π (C : Π z, x = z → Type v), C x (idp x) → C y p)
  (λ x C d, d) a x p C c

-- lemma 2.3.1
hott def Transport :=
Π (A : Type u) (P : A → Type v) (a b : A) (p : a = b), P a → P b

-- lemma 3.11.8
hott def SinglContr :=
Π (A : Type u) (a b : A) (p : a = b), @Id (singl a) ⟨a, idp a⟩ ⟨b, p⟩

hott def Ind.transport (φ : Ind.{u, v}) : Transport.{u, v} :=
λ A P, φ A (λ x y p, P x → P y) (λ x d, d)

hott def Ind.singlContr (φ : Ind.{u, u}) : SinglContr.{u} :=
λ A a b p, φ A (λ x y p, @Id (singl x) ⟨x, idp x⟩ ⟨y, p⟩) (λ _, idp _) a b p

hott def Ind.based (φ : Ind.{u, u}) : Ind'.{u, u} :=
λ A a C c x p, Ind.transport φ (singl a) (λ d, C d.1 d.2)
  ⟨a, idp a⟩ ⟨x, p⟩ (Ind.singlContr φ A a x p) c

-- exercise 1.8

namespace Nat'
  def ind (C : ℕ → Type u) (c₀ : C 0) (cₛ : Π n, C n → C (n + 1)) : Π n, C n
  | Nat.zero   => c₀
  | Nat.succ n => cₛ n (ind C c₀ cₛ n)

  def rec {C : Type u} (c₀ : C) (cₛ : ℕ → C → C) : ℕ → C :=
  ind (λ _, C) c₀ cₛ

  def add : ℕ → ℕ → ℕ :=
  λ n, rec n (λ _, Nat.succ)

  def mult : ℕ → ℕ → ℕ :=
  λ n, rec 0 (λ _, add n)

  def exp : ℕ → ℕ → ℕ :=
  λ n, rec 1 (λ _, mult n)

  hott def addZero : Π n, add n 0 = n := idp

  hott def zeroAdd : Π n, add 0 n = n :=
  ind (λ n, add 0 n = n) (idp 0) (λ n p, Id.map Nat.succ p)

  hott def succAdd : Π n m, add (n + 1) m = add n m + 1 :=
  λ n, ind (λ m, add (n + 1) m = add n m + 1) (idp (n + 1)) (λ m p, Id.map Nat.succ p)

  hott def addComm : Π n m, add n m = add m n :=
  λ n, ind (λ m, add n m = add m n) (zeroAdd n)⁻¹
    (λ m p, (Id.map Nat.succ p) ⬝ (succAdd m n)⁻¹)

  hott def addAssoc : Π n m k, add n (add m k) = add (add n m) k :=
  λ n m, ind (λ k, add n (add m k) = add (add n m) k) (idp (add n m)) (λ k p, Id.map Nat.succ p)

  hott def oneMul : Π n, mult 1 n = n :=
  ind (λ n, mult 1 n = n) (idp 0) (λ n p, (addComm 1 (mult 1 n)) ⬝ Id.map Nat.succ p)

  hott def succMul : Π n m, mult (n + 1) m = add m (mult n m) :=
  λ n, ind (λ m, mult (n + 1) m = add m (mult n m)) (idp 0) (λ m p, calc
    mult (n + 1) (m + 1) = add n (mult (n + 1) m) + 1   : succAdd n (mult (n + 1) m)
                     ... = add n (add m (mult n m)) + 1 : Id.map (λ k, add n k + 1) p
                     ... = add (add n m) (mult n m) + 1 : Id.map Nat.succ (addAssoc n m (mult n m))
                     ... = add (add m n) (mult n m) + 1 : Id.map (λ k, add k (mult n m) + 1) (addComm n m)
                     ... = add m (add n (mult n m)) + 1 : Id.map Nat.succ (addAssoc m n (mult n m))⁻¹
                     ... = add (m + 1) (mult n (m + 1)) : (succAdd m (mult n (m + 1)))⁻¹)

  hott def mulOne : Π n, mult n 1 = n :=
  ind (λ n, mult n 1 = n) (idp 0) (λ n p,
    (succMul n 1) ⬝ (addComm 1 (mult n 1)) ⬝ Id.map Nat.succ p)

  hott def mulZero : Π n, mult n 0 = 0 := λ _, idp 0

  hott def zeroMul : Π n, mult 0 n = 0 :=
  ind (λ n, mult 0 n = 0) (idp 0) (λ n p, zeroAdd (mult 0 n) ⬝ p)

  hott def mulComm : Π n m, mult n m = mult m n :=
  λ n, ind (λ m, mult n m = mult m n) (zeroMul n)⁻¹
    (λ m p, Id.map (add n) p ⬝ (succMul m n)⁻¹)

  hott def mulDistrLeft : Π n m k, mult n (add m k) = add (mult n m) (mult n k) :=
  λ n m, ind (λ k, mult n (add m k) = add (mult n m) (mult n k)) (idp (mult n m)) (λ k p, calc
      mult n (add m (k + 1)) = add n (add (mult n m) (mult n k)) : Id.map (add n) p
                         ... = add (add (mult n m) (mult n k)) n : addComm _ _
                         ... = add (mult n m) (add (mult n k) n) : (addAssoc _ _ _)⁻¹
                         ... = add (mult n m) (mult n (k + 1))   : Id.map (add (mult n m)) (addComm _ _))

  hott def mulDistrRight : Π n m k, mult (add n m) k = add (mult n k) (mult m k) :=
  λ n m k, calc mult (add n m) k = mult k (add n m)          : mulComm _ _
                             ... = add (mult k n) (mult k m) : mulDistrLeft _ _ _
                             ... = add (mult n k) (mult m k) : bimap add (mulComm _ _) (mulComm _ _)

  hott def mulAssoc : Π n m k, mult n (mult m k) = mult (mult n m) k :=
  λ n m, ind (λ k, mult n (mult m k) = mult (mult n m) k) (idp 0) (λ k p, calc
    mult n (mult m (k + 1)) = add (mult n m) (mult n (mult m k)) : mulDistrLeft _ _ _
                        ... = add (mult n m) (mult (mult n m) k) : Id.map (add (mult n m)) p
                        ... = mult (mult n m) (k + 1)            : idp _)
end Nat'

-- exercise 1.9

def fin (n : ℕ) : Type := Σ m, m + 1 ≤ n

hott def vin.fmax (n : ℕ) : fin (n + 1) :=
⟨n, Theorems.Nat.max.refl (n + 1)⟩

-- exercise 1.10

namespace Nat'
  hott def iterate {α : Type u} (f : α → α) : ℕ → (α → α) :=
  @rec (α → α) idfun (λ _ g, f ∘ g)

  hott def ack : ℕ → ℕ → ℕ :=
  rec Nat.succ (λ m φ n, iterate φ (n + 1) 1)

  example (n : ℕ) : ack 0 n = n + 1 :=
  by reflexivity

  example (m : ℕ) : ack (m + 1) 0 = ack m 1 :=
  by reflexivity

  example (m n : ℕ) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) :=
  by reflexivity
end Nat'

-- exercise 1.11

example (α : Type u) : (¬¬¬α) → (¬α) :=
λ φ x, φ (λ ψ, ψ x)

-- exercise 1.12

example (α : Type u) (β : Type v) : α → (β → α) :=
λ a b, a

example (α : Type u) : α → ¬¬α :=
λ a φ, φ a

example (α : Type u) (β : Type v) : (¬α) + (¬β) → ¬(α × β) :=
λ φ w, @Coproduct.elim (¬α) (¬β) 𝟎 (λ ψ, ψ w.1) (λ ψ, ψ w.2) φ

-- exercise 1.13

example (α : Type u) : ¬¬(α + ¬α) :=
λ φ, φ (Coproduct.inr (λ a, φ (Coproduct.inl a)))

-- exercise 1.14

/-
def f {α : Type u} (x : α) (p : x = x) : p = idp x :=
@Id.casesOn α x (λ y p, ???) x p (idp (idp x))
-/

-- exercise 1.15

hott def «Indiscernibility of Identicals» {A : Type u} (C : A → Type v)
  {a b : A} (p : a = b) : C a → C b :=
@Id.casesOn A a (λ x p, C a → C x) b p idfun

-- exercise 1.16

example : Π (i j : ℕ), i + j = j + i :=
Theorems.Nat.comm
