import GroundZero.HITs.Colimit
import GroundZero.Structures

open GroundZero.Types.Equiv (transport)
open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.Types.Nat

universe u v w

hott definition ind {C : ℕ → Type u} (zero : C 0) (succ : Π n, C n → C (n + 1)) : Π n, C n
| Nat.zero   => zero
| Nat.succ n => succ n (ind zero succ n)

hott definition inw : ℕ → ℕ + 𝟏
| Nat.zero   => Coproduct.inr ★
| Nat.succ n => Coproduct.inl n

hott definition outw : ℕ + 𝟏 → ℕ
| Coproduct.inr _ => Nat.zero
| Coproduct.inl n => Nat.succ n

hott lemma natUnitEqv : ℕ ≃ ℕ + 𝟏 :=
begin
  fapply Equiv.intro; exact inw; exact outw;
  { intro n; induction n using Nat.casesOn <;> reflexivity };
  { intro n; induction n using Sum.casesOn <;> reflexivity }
end

hott theorem equivAddition {A : Type u} {B : Type v} (C : Type w) (e : A ≃ B) : A + C ≃ B + C :=
begin
  let f : A + C → B + C := λ x, match x with
  | Coproduct.inl a => Coproduct.inl (e a)
  | Coproduct.inr c => Coproduct.inr c;
  let g : B + C → A + C := λ x, match x with
  | Coproduct.inl b => Coproduct.inl (e.left b)
  | Coproduct.inr c => Coproduct.inr c;

  existsi f; apply Prod.mk <;> existsi g;
  { intro x; induction x using Sum.casesOn;
    apply ap Sum.inl; apply e.leftForward; reflexivity };
  { intro x; induction x using Sum.casesOn;
    apply ap Sum.inl; apply e.forwardLeft; reflexivity }
end

hott example : ℕ ≃ (ℕ + 𝟏) + 𝟏 :=
begin transitivity; exact natUnitEqv; apply equivAddition; exact natUnitEqv end

hott definition natPlusUnit : Π n, ℕ ≃ pt ℕ n
| Nat.zero   => Equiv.ideqv _
| Nat.succ n => Equiv.trans natUnitEqv (equivAddition 𝟏 (natPlusUnit n))

hott definition liftUnit (n : ℕ) : pt 𝟏 n → pt 𝟏 (n + 1) :=
Coproduct.inl

hott definition liftToTop (x : 𝟏) : Π n, pt 𝟏 n
| Nat.zero   => x
| Nat.succ n => Coproduct.inl (liftToTop x n)

hott definition Iterated :=
HITs.Colimit (pt 𝟏) liftUnit

hott definition Iterated.encode : ℕ → Iterated
| Nat.zero   => HITs.Colimit.inclusion 0 ★
| Nat.succ n => HITs.Colimit.inclusion (n + 1) (Coproduct.inr ★)

hott definition code : ℕ → ℕ → Type
| Nat.zero,   Nat.zero   => 𝟏
| Nat.succ m, Nat.zero   => 𝟎
| Nat.zero,   Nat.succ n => 𝟎
| Nat.succ m, Nat.succ n => code m n

hott definition r : Π n, code n n
| Nat.zero   => ★
| Nat.succ n => r n

hott definition encode {m n : ℕ} (p : m = n) : code m n :=
transport (code m) p (r m)

hott definition decode : Π {m n : ℕ}, code m n → m = n
| Nat.zero,   Nat.zero,   p => idp 0
| Nat.succ m, Nat.zero,   p => Proto.Empty.elim p
| Nat.zero,   Nat.succ n, p => Proto.Empty.elim p
| Nat.succ m, Nat.succ n, p => ap Nat.succ (decode p)

hott lemma decodeEncodeIdp : Π m, decode (encode (idp m)) = idp m
| Nat.zero   => idp _
| Nat.succ m => ap _ (decodeEncodeIdp m)

hott corollary decodeEncode {m n : ℕ} (p : m = n) : decode (encode p) = p :=
begin induction p; apply decodeEncodeIdp end

hott lemma encodeDecode : Π {m n : ℕ} (p : code m n), encode (decode p) = p
| Nat.zero,   Nat.zero,   ★ => idp ★
| Nat.succ m, Nat.zero,   p => Proto.Empty.elim p
| Nat.zero,   Nat.succ n, p => Proto.Empty.elim p
| Nat.succ m, Nat.succ n, p =>
begin
  transitivity; symmetry;
  apply @Equiv.transportComp ℕ ℕ (code (m + 1)) m n
        Nat.succ (decode p) (r (m + 1));
  apply encodeDecode
end

hott theorem recognize (m n : ℕ) : m = n ≃ code m n :=
Equiv.intro encode decode decodeEncode encodeDecode

end GroundZero.Types.Nat
