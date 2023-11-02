import GroundZero.Theorems.Nat
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

hott def abs : ℤ → ℕ
| pos n => n
| neg n => n + 1

hott def plus : ℕ → ℤ := Integer.pos

hott def minus : ℕ → ℤ
| Nat.zero   => pos 0
| Nat.succ n => neg n

hott def negate : ℤ → ℤ
| pos Nat.zero     => pos 0
| pos (Nat.succ n) => neg n
| neg n            => pos (n + 1)

instance : Neg ℤ := ⟨negate⟩

hott def sgn : ℤ → ℤ
| pos Nat.zero     => 0
| pos (Nat.succ n) => 1
| neg n            => -1

hott def signum : ℤ → (ℕ → ℤ)
| pos _ => plus
| neg _ => minus

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

hott def auxsub : ℕ → ℕ → ℤ
| m,          Nat.zero   => pos m
| Nat.zero,   Nat.succ n => neg n
| Nat.succ m, Nat.succ n => auxsub m n

hott def add : ℤ → ℤ → ℤ
| neg x, neg y => neg (x + y + 1)
| neg x, pos y => auxsub y (x + 1)
| pos x, neg y => auxsub x (y + 1)
| pos x, pos y => pos (x + y)
instance : Add ℤ := ⟨add⟩

hott def sub (x y : ℤ) := x + (-y)
instance : Sub ℤ := ⟨sub⟩

hott def mul : ℤ → ℤ → ℤ
| neg x, neg y => plus  ((x + 1) * (y + 1))
| neg x, pos y => minus ((x + 1) * y)
| pos x, neg y => minus (x * (y + 1))
| pos x, pos y => plus  (x * y)
instance : Mul ℤ := ⟨mul⟩

hott def addZero (x : ℤ) : x + 0 = x :=
begin induction x using Sum.casesOn <;> reflexivity end

hott def zeroAdd (x : ℤ) : 0 + x = x :=
begin
  induction x using Sum.casesOn;
  { apply Id.map pos; apply Nat.zeroPlus };
  { apply Id.map neg; reflexivity }
end

hott def auxsubAsymm : Π x y, auxsub x y = negate (auxsub y x)
| Nat.zero,   Nat.zero   => idp _
| Nat.succ m, Nat.zero   => idp _
| Nat.zero,   Nat.succ n => idp _
| Nat.succ m, Nat.succ n => auxsubAsymm m n

hott def addComm : Π (x y : ℤ), x + y = y + x
| neg x, neg y => Id.map neg ((Nat.succPlus x y)⁻¹ ⬝ Nat.comm _ _)
| neg x, pos y => idp _
| pos x, neg y => idp _
| pos x, pos y => Id.map pos (Nat.comm _ _)

hott def auxsubZeroRight : Π (n : Nat), auxsub n 0 = pos n
| Nat.zero   => idp 0
| Nat.succ n => idp (pos (n + 1))

hott def auxsubZeroLeft : Π (n : ℕ), auxsub 0 n = auxsucc n
| Nat.zero   => idp 0
| Nat.succ n => idp (neg n)

hott def auxsubSucc : Π (n m : ℕ), auxsub (n + 1) m = auxsub n m + 1
| Nat.zero,   Nat.zero   => idp _
| Nat.succ n, Nat.zero   => idp _
| Nat.zero,   Nat.succ m => idp _
| Nat.succ n, Nat.succ m => auxsubSucc n m

hott def auxsubNeg : Π (n m : ℕ), auxsub n m = negate (auxsub m n)
| Nat.zero,   Nat.zero   => idp _
| Nat.succ m, Nat.zero   => idp _
| Nat.zero,   Nat.succ m => idp _
| Nat.succ n, Nat.succ m => auxsubNeg n m

hott def succAuxsub : Π (n m : ℕ), succ (auxsub n m) = auxsub (n + 1) m
| Nat.zero,   Nat.zero   => idp _
| Nat.succ n, Nat.zero   => idp _
| Nat.zero,   Nat.succ m => (auxsubZeroLeft _)⁻¹
| Nat.succ n, Nat.succ m => succAuxsub n m

hott def predAuxsub : Π (n m : ℕ), pred (auxsub n m) = auxsub n (m + 1)
| Nat.zero,   Nat.zero   => idp _
| Nat.succ n, Nat.zero   => (auxsubZeroRight _)⁻¹
| Nat.zero,   Nat.succ m => idp _
| Nat.succ n, Nat.succ m => predAuxsub n m

noncomputable hott def set : hset ℤ :=
by apply ua.coproductSet <;> apply Nat.natIsSet

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

hott def succToAdd : Π (z : ℤ), z + 1 = succ z
| neg Nat.zero     => idp _
| neg (Nat.succ _) => idp _
| pos n            => idp _

hott def predToSub : Π (z : ℤ), z - 1 = pred z
| neg n            => idp _
| pos Nat.zero     => idp _
| pos (Nat.succ _) => auxsubZeroRight _

hott def succPlus : Π (i j : ℤ), succ i + j = succ (i + j)
| neg Nat.zero,     neg y => ap neg (Nat.zeroPlus _)⁻¹
| neg (Nat.succ x), neg y => ap neg (Nat.assoc _ _ _ ⬝ (Nat.succPlus _ _)⁻¹)
| neg Nat.zero,     pos y => ap pos (Nat.zeroPlus _) ⬝ (auxsubZeroRight _)⁻¹ ⬝ (succPred _)⁻¹ ⬝ ap succ (predAuxsub _ _)
| neg (Nat.succ x), pos y => (succPred _)⁻¹ ⬝ ap succ (predAuxsub _ _)
| pos Nat.zero,     neg y => (succPred _)⁻¹ ⬝ ap succ (predAuxsub _ _)
| pos (Nat.succ x), neg y => (succAuxsub _ _)⁻¹
| pos x,            pos y => ap pos (Nat.succPlus _ _)

hott def plusSucc (i j : ℤ) : i + succ j = succ (i + j) :=
addComm _ _ ⬝ succPlus _ _ ⬝ ap succ (addComm _ _)

hott def predPlus : Π (i j : ℤ), pred i + j = pred (i + j)
| neg x,            neg y => ap neg (ap Nat.succ (Nat.succPlus _ _))
| neg Nat.zero,     pos y => (predAuxsub _ _)⁻¹
| neg (Nat.succ x), pos y => (predAuxsub _ _)⁻¹
| pos Nat.zero,     neg y => ap neg (Nat.assoc _ _ _ ⬝ Nat.zeroPlus _) ⬝ (ap pred (auxsubZeroLeft _) ⬝ predSucc (neg (y + 1)))⁻¹
| pos (Nat.succ x), neg y => (predAuxsub _ _)⁻¹
| pos Nat.zero,     pos y => (predAuxsub _ _)⁻¹ ⬝ ap pred (auxsubZeroRight _ ⬝ ap pos (Nat.zeroPlus _)⁻¹)
| pos (Nat.succ x), pos y => (predSucc _)⁻¹ ⬝ ap (pred ∘ pos) (Nat.succPlus _ _)⁻¹

hott def plusPred (i j : ℤ) : i + pred j = pred (i + j) :=
addComm _ _ ⬝ predPlus _ _ ⬝ ap pred (addComm _ _)

end Integer

end GroundZero.Types
