import GroundZero.Theorems.Nat
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

@[matchPattern] def Integer.pos : ℕ → ℤ := Coproduct.inl
@[matchPattern] def Integer.neg : ℕ → ℤ := Coproduct.inr

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

hott def auxsubZeroRight (n : Nat) : auxsub n 0 = pos n :=
begin induction n using Nat.casesOn <;> reflexivity end

hott def auxsubSucc : Π (n m : ℕ), auxsub (n + 1) m = auxsub n m + 1
| Nat.zero,   Nat.zero   => idp _
| Nat.succ m, Nat.zero   => idp _
| Nat.zero,   Nat.succ n => idp _
| Nat.succ m, Nat.succ n => auxsubSucc m n

hott def auxsubNeg : Π (n m : ℕ), auxsub n m = negate (auxsub m n)
| Nat.zero,   Nat.zero   => idp _
| Nat.succ m, Nat.zero   => idp _
| Nat.zero,   Nat.succ n => idp _
| Nat.succ m, Nat.succ n => auxsubNeg m n

noncomputable hott def set : hset ℤ :=
by apply ua.coproductSet <;> apply Nat.natIsSet

section
  variable {π : ℤ → Type u} (π₀ : π 0) (πsucc : Π x, π x → π (succ x)) (πpred : Π x, π x → π (pred x))

  hott def indpos : Π n, π (pos n)
  | Nat.zero    => π₀
  | Nat.succ n => πsucc (pos n) (indpos n)

  hott def indneg : Π n, π (neg n)
  | Nat.zero   => πpred 0 π₀
  | Nat.succ n => πpred (neg n) (indneg n)

  hott def indsp : Π x, π x
  | neg n => indneg π₀ πpred n
  | pos n => indpos π₀ πsucc n
end

hott def succToAdd : Π (z : ℤ), z + 1 = succ z
| neg Nat.zero     => idp _
| neg (Nat.succ _) => idp _
| pos n            => idp _

hott def predToSub : Π (z : ℤ), z - 1 = pred z
| neg n            => idp _
| pos Nat.zero     => idp _
| pos (Nat.succ _) => auxsubZeroRight _

end Integer

end GroundZero.Types