import GroundZero.Theorems.Nat

open GroundZero.Types.Equiv (bimap)
open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Theorems
open GroundZero

namespace GroundZero.Types

/-
  +2 = pos 2
  +1 = pos 1
   0 = pos 0
  −1 = neg 0
  −2 = neg 1
-/

def Integer := ℕ + ℕ
notation "ℤ" => Integer

@[match_pattern] def Integer.pos : ℕ → ℤ := Coproduct.inl
@[match_pattern] def Integer.neg : ℕ → ℤ := Coproduct.inr

instance (n : ℕ) : OfNat ℤ n := ⟨Integer.pos n⟩

namespace Integer

instance : ToString ℤ :=
⟨λ | pos n => toString n
   | neg n => "-" ++ toString (n + 1)⟩

hott def auxsucc : ℕ → ℤ
| Nat.zero   => pos 0
| Nat.succ n => neg n

hott def succ : ℤ → ℤ
| neg u => auxsucc u
| pos v => pos (v + 1)

hott def auxpred : ℕ → ℤ
| Nat.zero   => neg 0
| Nat.succ n => pos n

hott def pred : ℤ → ℤ
| neg u => neg (u + 1)
| pos v => auxpred v

hott def succPred : Π z, succ (pred z) = z
| neg _            => idp _
| pos Nat.zero     => idp _
| pos (Nat.succ _) => idp _

hott def predSucc : Π z, pred (succ z) = z
| neg Nat.zero     => idp _
| neg (Nat.succ _) => idp _
| pos _            => idp _

hott def succEquiv : ℤ ≃ ℤ :=
⟨succ, (⟨pred, predSucc⟩, ⟨pred, succPred⟩)⟩

section
  universe u

  variable {π : ℤ → Type u} (π₀ : π 0)
           (πsucc : Π x, π x → π (succ x))
           (πpred : Π x, π x → π (pred x))
           (coh₁ : Π p z, πpred _ (πsucc p z) =[predSucc _] z)
           (coh₂ : Π p z, πsucc _ (πpred p z) =[succPred _] z)

  hott def indpos : Π n, π (pos n)
  | Nat.zero   => π₀
  | Nat.succ n => πsucc (pos n) (indpos n)

  hott def indneg : Π n, π (neg n)
  | Nat.zero   => πpred 0 π₀
  | Nat.succ n => πpred (neg n) (indneg n)

  hott def indsp : Π z, π z
  | neg n => indneg π₀ πpred n
  | pos n => indpos π₀ πsucc n

  hott def indspβ₁ : indsp π₀ πsucc πpred 0 = π₀ :=
  by reflexivity

  hott def indspβ₂ : Π z, indsp π₀ πsucc πpred (succ z) = πsucc z (indsp π₀ πsucc πpred z)
  | neg Nat.zero     => (coh₂ (pos 0) _)⁻¹
  | neg (Nat.succ n) => (coh₂ (neg n) _)⁻¹
  | pos n            => idp _

  hott def indspβ₃ : Π z, indsp π₀ πsucc πpred (pred z) = πpred z (indsp π₀ πsucc πpred z)
  | neg n            => idp _
  | pos Nat.zero     => idp _
  | pos (Nat.succ n) => (coh₁ (pos n) _)⁻¹
end

section
  universe u

  variable {π : Type u} (π₀ : π)
           (πsucc : π → π) (πpred : π → π)
           (coh₁ : πpred ∘ πsucc ~ id)
           (coh₂ : πsucc ∘ πpred ~ id)

  hott def recpos : ℕ → π
  | Nat.zero   => π₀
  | Nat.succ n => πsucc (recpos n)

  hott def recneg : ℕ → π
  | Nat.zero   => πpred π₀
  | Nat.succ n => πpred (recneg n)

  hott def recsp : ℤ → π
  | neg n => recneg π₀ πpred n
  | pos n => recpos π₀ πsucc n

  hott def recspβ₁ : recsp π₀ πsucc πpred 0 = π₀ :=
  by reflexivity

  hott def recspβ₂ : Π z, recsp π₀ πsucc πpred (succ z) = πsucc (recsp π₀ πsucc πpred z)
  | neg Nat.zero     => (coh₂ _)⁻¹
  | neg (Nat.succ n) => (coh₂ _)⁻¹
  | pos n            => idp _

  hott def recspβ₃ : Π z, recsp π₀ πsucc πpred (pred z) = πpred (recsp π₀ πsucc πpred z)
  | neg n            => idp _
  | pos Nat.zero     => idp _
  | pos (Nat.succ n) => (coh₁ _)⁻¹
end

hott def abs : ℤ → ℕ
| pos n => n
| neg n => n + 1

hott def add : ℤ → ℤ → ℤ :=
λ z, recsp z succ pred

instance : Add ℤ := ⟨add⟩

hott def negate : ℤ → ℤ
| pos n => auxsucc n
| neg n => pos (n + 1)

instance : Neg ℤ := ⟨negate⟩

hott def sgn : ℤ → ℤ
| pos Nat.zero     =>  0
| pos (Nat.succ n) =>  1
| neg n            => -1

hott def sub (x y : ℤ) := x + (-y)
instance : Sub ℤ := ⟨sub⟩

hott lemma plusSucc (i j : ℤ) : i + succ j = succ (i + j) :=
begin apply recspβ₂; apply succPred end

hott lemma plusPred (i j : ℤ) : i + pred j = pred (i + j) :=
begin apply recspβ₃; apply predSucc end

hott def addZero (x : ℤ) : x + 0 = x :=
by reflexivity

hott def zeroAdd (x : ℤ) : 0 + x = x :=
begin
  induction x using indsp; reflexivity;
  { transitivity; apply plusSucc; apply ap; assumption };
  { transitivity; apply plusPred; apply ap; assumption }
end

hott def succPlus (i j : ℤ) : succ i + j = succ (i + j) :=
begin
  induction j using indsp; reflexivity;
  { transitivity; apply plusSucc; apply ap;
    transitivity; assumption; symmetry; apply plusSucc };
  { transitivity; apply plusPred; transitivity;
    apply ap pred; assumption; transitivity; apply predSucc;
    transitivity; symmetry; apply succPred; apply ap succ;
    symmetry; apply plusPred }
end

hott def predPlus (i j : ℤ) : pred i + j = pred (i + j) :=
begin
  induction j using indsp; reflexivity;
  { transitivity; apply plusSucc; transitivity;
    apply ap succ; assumption; transitivity; apply succPred;
    transitivity; symmetry; apply predSucc; apply ap pred;
    symmetry; apply plusSucc };
  { transitivity; apply plusPred; apply ap pred;
    transitivity; assumption; symmetry; apply plusPred }
end

hott def addComm (x y : ℤ) : x + y = y + x :=
begin
  induction y using indsp; symmetry; apply zeroAdd;
  { transitivity; apply plusSucc; transitivity; apply ap succ;
    assumption; symmetry; apply succPlus };
  { transitivity; apply plusPred; transitivity; apply ap pred;
    assumption; symmetry; apply predPlus }
end

hott def diff : ℕ → ℕ → ℤ
| m,          Nat.zero   => pos m
| Nat.zero,   Nat.succ n => neg n
| Nat.succ m, Nat.succ n => diff m n

hott def diffAsymm : Π x y, diff x y = negate (diff y x)
| Nat.zero,   Nat.zero   => idp _
| Nat.succ m, Nat.zero   => idp _
| Nat.zero,   Nat.succ n => idp _
| Nat.succ m, Nat.succ n => diffAsymm m n

hott def diffZeroRight : Π (n : Nat), diff n 0 = pos n
| Nat.zero   => idp 0
| Nat.succ n => idp (pos (n + 1))

hott def diffZeroLeft : Π (n : ℕ), diff 0 n = auxsucc n
| Nat.zero   => idp 0
| Nat.succ n => idp (neg n)

hott def diffSucc : Π (n m : ℕ), diff (n + 1) m = diff n m + 1
| Nat.zero,   Nat.zero   => idp _
| Nat.succ n, Nat.zero   => idp _
| Nat.zero,   Nat.succ m => diffZeroLeft _
| Nat.succ n, Nat.succ m => diffSucc n m

hott def succDiff : Π (n m : ℕ), succ (diff n m) = diff (n + 1) m
| Nat.zero,   Nat.zero   => idp _
| Nat.succ n, Nat.zero   => idp _
| Nat.zero,   Nat.succ m => (diffZeroLeft _)⁻¹
| Nat.succ n, Nat.succ m => succDiff n m

hott def predDiff : Π (n m : ℕ), pred (diff n m) = diff n (m + 1)
| Nat.zero,   Nat.zero   => idp _
| Nat.succ n, Nat.zero   => (diffZeroRight _)⁻¹
| Nat.zero,   Nat.succ m => idp _
| Nat.succ n, Nat.succ m => predDiff n m

hott def diffAddLeft (n : ℕ) : Π (m : ℕ), diff (n + m) m = pos n
| Nat.zero   => diffZeroRight n
| Nat.succ m => diffAddLeft n m

hott def diffAddRight (n : ℕ) : Π (m : ℕ), diff m (n + m) = auxsucc n
| Nat.zero   => diffZeroLeft n
| Nat.succ m => diffAddRight n m

noncomputable hott def set : hset ℤ :=
by apply ua.coproductSet <;> apply Nat.natIsSet

hott def succToAdd (z : ℤ) : z + 1 = succ z :=
by reflexivity

hott def predToSub (z : ℤ) : z - 1 = pred z :=
by apply plusPred z 0

hott def mul : ℤ → ℤ → ℤ :=
λ i, recsp 0 (λ j, j + i) (λ j, j - i)

instance : Mul ℤ := ⟨mul⟩

hott lemma negateSucc : Π (i : ℤ), negate (succ i) = pred (negate i)
| pos Nat.zero     => idp _
| pos (Nat.succ _) => idp _
| neg Nat.zero     => idp _
| neg (Nat.succ _) => idp _

hott lemma negatePred : Π (i : ℤ), negate (pred i) = succ (negate i)
| pos Nat.zero     => idp _
| pos (Nat.succ _) => idp _
| neg Nat.zero     => idp _
| neg (Nat.succ _) => idp _

hott lemma negateNegate : Π (i : ℤ), negate (negate i) = i
| pos Nat.zero     => idp _
| pos (Nat.succ n) => idp _
| neg n            => idp _

hott lemma addSub (i j : ℤ) : (i + j) - j = i :=
begin
  induction j using indsp; reflexivity;
  { transitivity; apply bimap add; apply plusSucc; apply negateSucc;
    transitivity; apply succPlus; transitivity; apply ap succ;
    apply plusPred; transitivity; apply succPred; assumption };
  { transitivity; apply bimap add; apply plusPred; apply negatePred;
    transitivity; apply predPlus; transitivity; apply ap pred;
    apply plusSucc; transitivity; apply predSucc; assumption }
end

hott lemma subAdd (i j : ℤ) : (i - j) + j = i :=
begin transitivity; apply ap (add _); symmetry; apply negateNegate; apply addSub end

hott def multZero (i : ℤ) : i * 0 = 0 :=
by reflexivity

hott def multSucc (i j : ℤ) : i * succ j = i * j + i :=
begin apply recspβ₂; intro; apply subAdd end

hott def multPred (i j : ℤ) : i * pred j = i * j - i :=
begin apply recspβ₃; intro; apply addSub end

end Integer

end GroundZero.Types
