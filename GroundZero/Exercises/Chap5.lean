import GroundZero.Exercises.Chap4

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
