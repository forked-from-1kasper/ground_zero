import GroundZero.HITs.Colimit
import GroundZero.Structures

open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.Types.Nat

universe u v w

def glue : ℕ → ℕ + 𝟏
| Nat.zero   => Coproduct.inr ★
| Nat.succ n => Coproduct.inl n

def peelOff : ℕ + 𝟏 → ℕ
| Coproduct.inr _ => Nat.zero
| Coproduct.inl n => Nat.succ n

hott def closedNat : ℕ ≃ ℕ + 𝟏 :=
begin
  existsi glue; apply Prod.mk <;> existsi peelOff <;> intro n;
  { induction n using Nat.casesOn <;> reflexivity };
  { induction n using Sum.casesOn <;> reflexivity }
end

hott def equivAddition {A : Type u} {B : Type v} (C : Type w) (e : A ≃ B) : A + C ≃ B + C :=
begin
  let f : A + C → B + C := λ x, match x with
  | Coproduct.inl a => Coproduct.inl (e a)
  | Coproduct.inr c => Coproduct.inr c;
  let g : B + C → A + C := λ x, match x with
  | Coproduct.inl b => Coproduct.inl (e.left b)
  | Coproduct.inr c => Coproduct.inr c;

  existsi f; apply Prod.mk <;> existsi g;
  { intro x; induction x using Sum.casesOn;
    apply Id.map Sum.inl; apply e.leftForward; reflexivity };
  { intro x; induction x using Sum.casesOn;
    apply Id.map Sum.inl; apply e.forwardLeft; reflexivity }
end

example : ℕ ≃ (ℕ + 𝟏) + 𝟏 :=
begin transitivity; exact closedNat; apply equivAddition; exact closedNat end

hott def natPlusUnit : Π n, ℕ ≃ pt ℕ n
| Nat.zero   => Equiv.ideqv _
| Nat.succ n => Equiv.trans closedNat (equivAddition 𝟏 (natPlusUnit n))

hott def liftUnit (n : ℕ) : pt 𝟏 n → pt 𝟏 (n + 1) :=
Coproduct.inl

hott def liftToTop (x : 𝟏) : Π n, pt 𝟏 n
| Nat.zero   => x
| Nat.succ n => Coproduct.inl (liftToTop x n)

hott def Iterated := HITs.Colimit (pt 𝟏) liftUnit

def Iterated.encode : ℕ → Iterated
| Nat.zero   => HITs.Colimit.inclusion 0 ★
| Nat.succ n => HITs.Colimit.inclusion (n + 1) (Coproduct.inr ★)

hott def code : ℕ → ℕ → Type
| Nat.zero,   Nat.zero   => 𝟏
| Nat.succ m, Nat.zero   => 𝟎
| Nat.zero,   Nat.succ n => 𝟎
| Nat.succ m, Nat.succ n => code m n

hott def r : Π n, code n n
| Nat.zero   => ★
| Nat.succ n => r n

hott def encode {m n : ℕ} (p : m = n) : code m n :=
Equiv.subst p (r m)

hott def decode : Π {m n : ℕ}, code m n → m = n
| Nat.zero,   Nat.zero,   p => idp 0
| Nat.succ m, Nat.zero,   p => Proto.Empty.elim p
| Nat.zero,   Nat.succ n, p => Proto.Empty.elim p
| Nat.succ m, Nat.succ n, p => Id.map Nat.succ (decode p)

hott def decodeEncodeIdp : Π m, decode (encode (idp m)) = idp m
| Nat.zero   => idp _
| Nat.succ m => Id.map _ (decodeEncodeIdp m)

hott def decodeEncode {m n : ℕ} (p : m = n) : decode (encode p) = p :=
begin induction p; apply decodeEncodeIdp end

hott def encodeDecode : Π {m n : ℕ} (p : code m n), encode (decode p) = p
| Nat.zero,   Nat.zero,   ★ => idp ★
| Nat.succ m, Nat.zero,   p => Proto.Empty.elim p
| Nat.zero,   Nat.succ n, p => Proto.Empty.elim p
| Nat.succ m, Nat.succ n, p => begin
  transitivity; symmetry;
  apply @Equiv.transportComp ℕ ℕ (code (m + 1)) m n
        Nat.succ (decode p) (r (m + 1));
  apply encodeDecode
end

hott def recognize (m n : ℕ) : m = n ≃ code m n :=
⟨encode, (⟨decode, decodeEncode⟩, ⟨decode, encodeDecode⟩)⟩

end GroundZero.Types.Nat