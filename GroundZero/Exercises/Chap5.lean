import GroundZero.Exercises.Chap4
import GroundZero.Types.Lost

open GroundZero.Types
open GroundZero.Proto
open GroundZero

universe u v w

-- Exercise 5.2

namespace «5.2»
  open Nat (zero succ)

  hott definition idfun₁ : ℕ → ℕ :=
  λ n, n

  hott definition idfun₂ : ℕ → ℕ
  | zero   => zero
  | succ n => succ (idfun₂ n)

  hott definition ez : ℕ         := zero
  hott definition es : ℕ → ℕ → ℕ := λ n m, succ m

  #failure idfun₁ ≡ idfun₂

  #success idfun₁ zero ≡ ez
  #success idfun₂ zero ≡ ez

  variable (n : ℕ)
  #success idfun₁ (succ n) ≡ es n (idfun₁ n)
  #success idfun₂ (succ n) ≡ es n (idfun₂ n)
end «5.2»

-- Exercise 5.3

namespace «5.3»
  open Nat (zero succ)

  variable {E : Type u} {e : E}

  hott definition ez₁ : E         := e
  hott definition es₁ : ℕ → E → E := λ n ε, ε

  hott definition ez₂ : E         := e
  hott definition es₂ : ℕ → E → E := λ n _, e

  #failure @es₁ E ≡ @es₂ E e : ℕ → E → E

  hott definition f : ℕ → E :=
  λ _, e

  #success (@f E e) zero ≡ @ez₁ E e
  #success (@f E e) zero ≡ @ez₂ E e

  variable (n : ℕ)
  #success (@f E e) (succ n) ≡ (@es₁ E)   n (@f E e n)
  #success (@f E e) (succ n) ≡ (@es₂ E e) n (@f E e n)
end «5.3»

-- Exercise 5.4

hott example (E : 𝟐 → Type u) : (E false × E true) ≃ (Π b, E b) :=
familyOnBool

-- Exercise 5.7

namespace «5.7»
  variable (C : Type) (c : (C → 𝟎) → C) (elim : Π (P : Type), ((C → 𝟎) → (P → 𝟎) → P) → C → P)

  hott example : 𝟎 :=
  have nc := elim 𝟎 (λ g i, g (c g));
  nc (c nc)
end «5.7»

-- Exercise 5.8

namespace «5.8»
  variable (D : Type) (scott : (D → D) → D)
           (elim : Π (P : Type), ((D → D) → (D → P) → P) → D → P)

  hott example : 𝟎 :=
  have nd := elim 𝟎 (λ f g, g (scott f));
  nd (scott idfun)

  -- Computation rule seems to be not required here.
  variable (elimβrule : Π P h α, elim P h (scott α) = h α (elim P h ∘ α))
end «5.8»

-- Exercise 5.9

namespace «5.9»
  variable {A L : Type} (lawvere : (L → A) → L) (elim : Π (P : Type), ((L → A) → P) → L → P)

  hott definition fix (f : A → A) : A :=
  have φ := elim A (λ α, f (α (lawvere α)));
  φ (lawvere φ)

  variable (elimβrule : Π P h α, elim P h (lawvere α) = h α)

  hott theorem hasFixpoint (f : A → A) (a : A) : f (fix lawvere elim f) = fix lawvere elim f :=
  begin symmetry; apply elimβrule end
end «5.9»

-- Exercise 5.11

hott example (A : Type u) : Lost A ≃ 𝟎 :=
Lost.isZero
