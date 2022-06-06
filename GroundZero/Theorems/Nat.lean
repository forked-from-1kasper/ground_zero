import GroundZero.Theorems.UA
import GroundZero.Types.Nat

open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types

namespace GroundZero
namespace Theorems

namespace Nat
  universe u

  noncomputable hott def natIsSet' : hset ℕ
  | Nat.zero,   Nat.zero,   p, q => transport prop (ua (Nat.recognize 0 0))⁻¹ unitIsProp p q
  | Nat.succ m, Nat.zero,   p, q => Proto.Empty.elim (ua.succNeqZero p)
  | Nat.zero,   Nat.succ n, p, q => Proto.Empty.elim (ua.succNeqZero p⁻¹)
  | Nat.succ m, Nat.succ n, p, q =>
    transport prop (ua (Nat.recognize (m + 1) (n + 1)))⁻¹
      (transport prop (ua (Nat.recognize m n)) (natIsSet' m n)) p q

  def succInj {n m : ℕ} : Nat.succ n = Nat.succ m → n = m :=
  Nat.decode ∘ Nat.encode

  hott def natDecEq : Π (m n : ℕ), dec (m = n)
  | Nat.zero,   Nat.zero   => Sum.inl (idp 0)
  | Nat.succ m, Nat.zero   => Sum.inr ua.succNeqZero
  | Nat.zero,   Nat.succ n => Sum.inr (ua.succNeqZero ∘ Id.inv)
  | Nat.succ m, Nat.succ n =>
    match natDecEq m n with
    | Sum.inl p => Sum.inl (Id.map Nat.succ p)
    | Sum.inr φ => Sum.inr (φ ∘ succInj)

  hott def natIsSet : hset ℕ := Hedberg natDecEq

  hott def zeroPlus : Π (i : ℕ), 0 + i = i
  | Nat.zero   => idp 0
  | Nat.succ i => Id.map Nat.succ (zeroPlus i)

  hott def succPlus (i : ℕ) : Π j, Nat.succ i + j = Nat.succ (i + j)
  | Nat.zero   => idp _
  | Nat.succ j => Id.map Nat.succ (succPlus i j)

  hott def comm : Π (i j : ℕ), i + j = j + i
  | Nat.zero,   j => zeroPlus j
  | Nat.succ i, j => succPlus i j ⬝ Id.map Nat.succ (comm i j)

  hott def assoc (i j : ℕ) : Π k, (i + j) + k = i + (j + k)
  | Nat.zero   => idp (i + j)
  | Nat.succ k => Id.map Nat.succ (assoc i j k)

  hott def zeroMul : Π (i : ℕ), 0 * i = 0
  | Nat.zero   => idp 0
  | Nat.succ i => zeroMul i

  hott def oneMul : Π (i : ℕ), 1 * i = i
  | Nat.zero   => idp 0
  | Nat.succ i => Id.map Nat.succ (oneMul i)

  hott def mulOne (i : ℕ) : i * 1 = i := zeroPlus i

  hott def distribLeft (i : ℕ) : Π (j n : ℕ), n * (i + j) = n * i + n * j
  | Nat.zero,   n => idp _
  | Nat.succ j, n => Id.map (λ m, m + n) (distribLeft i j n) ⬝ assoc _ _ _

  hott def mulSucc (i : ℕ) : Π j, Nat.succ i * j = i * j + j
  | Nat.zero   => idp _
  | Nat.succ j => Id.map Nat.succ (Id.map (λ k, k + i) (mulSucc i j) ⬝ assoc _ _ _
                                ⬝ (assoc _ _ _ ⬝ Id.map _ (comm _ _))⁻¹)

  hott def mulComm (i : ℕ) : Π j, i * j = j * i
  | Nat.zero   => (zeroMul _)⁻¹
  | Nat.succ j => distribLeft j 1 i ⬝ (mulSucc j i ⬝ bimap Nat.add (mulComm i j)⁻¹ (mulOne i)⁻¹)⁻¹

  hott def distribRight (i j n : ℕ) : (i + j) * n = i * n + j * n :=
  mulComm (i + j) n ⬝ distribLeft _ _ _ ⬝ bimap Nat.add (mulComm _ _) (mulComm _ _)

  hott def oneNeqNPlusTwo (n : ℕ) : ¬(1 = n + 2) :=
  λ p, ua.succNeqZero (Id.map Nat.pred p)⁻¹

  def isEven (n : ℕ) := Σ m, n = m * 2
  def isOdd  (n : ℕ) := Σ m, n = m * 2 + 1

  hott def plusOnePlus {i j : ℕ} : i + 1 + j = (i + j) + 1 := calc
    i + 1 + j = i + (1 + j) : assoc _ _ _
          ... = i + (j + 1) : Id.map (Nat.add i) (comm 1 j)
          ... = (i + j) + 1 : idp _

  hott def assocTetra {i j k l : ℕ} : i + (j + k) + l = (i + j) + (k + l) := calc
    (i + (j + k)) + l = i + ((j + k) + l) : assoc _ _ _
                  ... = i + (j + (k + l)) : Id.map _ (assoc _ _ _)
                  ... = (i + j) + (k + l) : (assoc _ _ _)⁻¹

  hott def plusDiag (n : ℕ) : n * 2 = n + n :=
  Id.map (λ m, m + n) (zeroPlus _)

  hott def apart : ℕ → ℕ → Type
  | Nat.zero,   Nat.zero   => 𝟎
  | Nat.succ m, Nat.zero   => 𝟏
  | Nat.zero,   Nat.succ n => 𝟏
  | Nat.succ m, Nat.succ n => apart m n

  hott def max : ℕ → ℕ → ℕ
  | Nat.zero,   Nat.zero   => 0
  | Nat.succ m, Nat.zero   => m + 1
  | Nat.zero,   Nat.succ n => n + 1
  | Nat.succ m, Nat.succ n => max m n + 1

  hott def max.comm : Π (m n : ℕ), max m n = max n m
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ m, Nat.zero   => idp _
  | Nat.zero,   Nat.succ n => idp _
  | Nat.succ m, Nat.succ n => Id.map Nat.succ (comm _ _)

  hott def min : ℕ → ℕ → ℕ
  | Nat.zero,   Nat.zero   => 0
  | Nat.succ m, Nat.zero   => 0
  | Nat.zero,   Nat.succ n => 0
  | Nat.succ m, Nat.succ n => min m n + 1

  hott def min.comm : Π (m n : ℕ), min m n = min n m
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ m, Nat.zero   => idp _
  | Nat.zero,   Nat.succ n => idp _
  | Nat.succ m, Nat.succ n => Id.map Nat.succ (comm _ _)

  hott def max.refl : Π n, max n n = n
  | Nat.zero   => idp 0
  | Nat.succ n => Id.map Nat.succ (refl n)

  hott def min.refl : Π n, min n n = n
  | Nat.zero   => idp 0
  | Nat.succ n => Id.map Nat.succ (refl n)

  def le (n m : ℕ) := max n m = m
  infix:55 (priority := high) " ≤ " => le

  def ge (n m : ℕ) := m ≤ n
  infix:55 (priority := high) " ≥ " => ge

  hott def max.zeroLeft (n : ℕ) : max 0 n = n :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott def max.zeroRight (n : ℕ) : max n 0 = n :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott def min.zeroLeft (n : ℕ) : min 0 n = 0 :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott def min.zeroRight (n : ℕ) : min n 0 = 0 :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott def max.neZero {n : ℕ} : ¬(max (n + 1) 0 = 0) := ua.succNeqZero

  hott def max.zero : Π n, max n 0 = 0 → n = 0
  | Nat.zero,   _ => idp _
  | Nat.succ n, p => Proto.Empty.elim (max.neZero p)
  
  hott def le.prop (n m : ℕ) : prop (n ≤ m) := natIsSet _ _

  hott def max.assoc : Π n m k, max n (max m k) = max (max n m) k
  | Nat.zero,   Nat.zero,   Nat.zero   => idp _
  | Nat.zero,   Nat.zero,   Nat.succ k => idp _
  | Nat.zero,   Nat.succ m, Nat.zero   => idp _
  | Nat.zero,   Nat.succ m, Nat.succ k => max.zeroLeft _
  | Nat.succ n, Nat.zero,   Nat.zero   => idp _
  | Nat.succ n, Nat.zero,   Nat.succ k => idp _
  | Nat.succ n, Nat.succ m, Nat.zero   => idp _
  | Nat.succ n, Nat.succ m, Nat.succ k => Id.map Nat.succ (assoc _ _ _)

  hott def min.assoc : Π n m k, min n (min m k) = min (min n m) k
  | Nat.zero,   Nat.zero,   Nat.zero   => idp _
  | Nat.zero,   Nat.zero,   Nat.succ k => idp _
  | Nat.zero,   Nat.succ m, Nat.zero   => idp _
  | Nat.zero,   Nat.succ m, Nat.succ k => min.zeroLeft _
  | Nat.succ n, Nat.zero,   Nat.zero   => idp _
  | Nat.succ n, Nat.zero,   Nat.succ k => idp _
  | Nat.succ n, Nat.succ m, Nat.zero   => idp _
  | Nat.succ n, Nat.succ m, Nat.succ k => Id.map Nat.succ (assoc _ _ _)

  hott def le.trans {n m k : ℕ} : n ≤ m → m ≤ k → n ≤ k :=
  begin
    intros p q; change _ = _; transitivity;
    apply Id.map; exact q⁻¹; transitivity; apply max.assoc;
    transitivity; apply Id.map (max · k); exact p; exact q
  end

  instance : Transitive le := ⟨@le.trans⟩

  hott def le.inj (n m : ℕ) : n + 1 ≤ m + 1 → n ≤ m := Id.map Nat.pred
  hott def le.map (n m : ℕ) : n ≤ m → n + 1 ≤ m + 1 := Id.map Nat.succ

  hott def le.succ : Π (n : ℕ), n ≤ n + 1
  | Nat.zero   => idp _
  | Nat.succ n => Id.map Nat.succ (succ n)

  hott def le.step : Π (n m : ℕ), n ≤ m → n ≤ m + 1
  | Nat.zero,   m, _ => idp _
  | Nat.succ n, m, p => le.trans p (le.succ _)

  hott def minMax : Π (m n : ℕ), max m n = n → min m n = m
  | Nat.zero,   Nat.zero,   p => idp _
  | Nat.succ m, Nat.zero,   p => Proto.Empty.elim (max.neZero p)
  | Nat.zero,   Nat.succ n, p => idp _
  | Nat.succ m, Nat.succ n, p => Id.map Nat.succ (minMax m n (Id.map Nat.pred p))

  hott def le.max (n m : ℕ) : n ≤ max n m :=
  begin
    change _ = _; transitivity; apply max.assoc;
    apply Id.map (Nat.max · m); apply max.refl
  end

  hott def le.maxRev (n m : ℕ) : n ≤ Nat.max m n :=
  transport (le n) (max.comm n m) (le.max n m)

  hott def le.min : Π (n m : ℕ), le (min n m) m
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ n, Nat.zero   => idp _
  | Nat.zero,   Nat.succ m => idp _
  | Nat.succ n, Nat.succ m => Id.map Nat.succ (min n m)

  hott def le.minRev (n m : ℕ) : Nat.min m n ≤ m :=
  @transport ℕ (· ≤ m) (Nat.min n m) (Nat.min m n) (min.comm n m) (le.min n m)

  hott def le.asymm {n m : ℕ} (p : n ≤ m) (q : m ≤ n) : n = m :=
  q⁻¹ ⬝ max.comm _ _ ⬝ p

  hott def le.dec : Π (m n : ℕ), (m ≤ n) + (n + 1 ≤ m)
  | Nat.zero,   Nat.zero   => Sum.inl (idp _)
  | Nat.succ m, Nat.zero   => Sum.inr (Id.map Nat.succ (max.zeroLeft m))
  | Nat.zero,   Nat.succ n => Sum.inl (idp _)
  | Nat.succ m, Nat.succ n => Coproduct.elim (Sum.inl ∘ Id.map Nat.succ) (Sum.inr ∘ Id.map Nat.succ) (dec m n)

  hott def le.neSucc : Π (n : ℕ), ¬(n + 1 ≤ n)
  | Nat.zero   => max.neZero
  | Nat.succ n => λ p, neSucc n (le.inj _ _ p)

  hott def le.empty (m n : ℕ) : m ≤ n → ¬(n + 1 ≤ m) :=
  begin intros p q; apply le.neSucc n; transitivity; exact q; exact p end

  hott def le.neqSucc {n m : ℕ} (p : n ≠ m + 1) (q : n ≤ m + 1) : n ≤ m :=
  match le.dec n m with
  | Sum.inl r₁ => r₁
  | Sum.inr r₂ => Proto.Empty.elim (p (le.asymm q r₂))

  hott def le.leSucc : Π (n : ℕ), n ≤ n + 1
  | Nat.zero   => idp _
  | Nat.succ n => Id.map Nat.succ (leSucc n)

  hott def le.elim (ρ : ℕ → ℕ → Type u) (τ : Π n m k, ρ n m → ρ m k → ρ n k)
    (reflρ : Π n, ρ n n) (succρ : Π n, ρ n (n + 1)) {n : ℕ} : Π {m : ℕ}, n ≤ m → ρ n m
  | Nat.zero, p   => transport (ρ · 0) (max.zero _ p)⁻¹ (reflρ _)
  | Nat.succ m, p =>
    match natDecEq n (m + 1) with
    | Sum.inl q₁ => transport (ρ n) q₁ (reflρ _)
    | Sum.inr q₂ => τ n m _ (@elim ρ τ reflρ succρ n m (le.neqSucc q₂ p)) (succρ _)

  def dist : ℕ → ℕ → ℕ
  | Nat.zero,   Nat.zero   => 0
  | Nat.succ m, Nat.zero   => Nat.succ m
  | Nat.zero,   Nat.succ n => Nat.succ n
  | Nat.succ m, Nat.succ n => dist m n

  hott def dist.refl : Π (n : ℕ), dist n n = 0
  | Nat.zero   => idp 0
  | Nat.succ n => refl n

  hott def dist.identity : Π (n m : ℕ) (p : dist n m = 0), n = m
  | Nat.zero,   Nat.zero,   _ => idp 0
  | Nat.succ m, Nat.zero,   p => p
  | Nat.zero,   Nat.succ n, p => p⁻¹
  | Nat.succ m, Nat.succ n, p => Id.map Nat.succ (identity m n p)

  hott def dist.symm : Π (n m : ℕ), dist n m = dist m n
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ m, Nat.zero   => idp _
  | Nat.zero,   Nat.succ n => idp _
  | Nat.succ m, Nat.succ n => symm m n

  hott def dist.zeroLeft (n : ℕ) : dist n 0 = n :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott def dist.zeroRight (n : ℕ) : dist 0 n = n :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott def dist.succLeft : Π (n m : ℕ), dist (n + 1) m ≤ dist n m + 1
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ n, Nat.zero   => max.refl _
  | Nat.zero,   Nat.succ m => transport (· ≤ m + 2) (dist.zeroRight m)⁻¹ (le.trans (le.leSucc _) (le.leSucc _))
  | Nat.succ n, Nat.succ m => succLeft n m

  hott def max.leAdd : Π (n m : ℕ), le (max n m) (n + m)
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ n, Nat.zero   => max.refl _
  | Nat.zero,   Nat.succ m => transport (m + 1 ≤ ·) (zeroPlus _)⁻¹ (max.refl _)
  | Nat.succ n, Nat.succ m => le.trans (le.map (max n m) (n + m) (leAdd n m)) (begin
      apply transport (n + m + 1 ≤ ·); symmetry; transitivity;
      apply Nat.assoc n 1; transitivity; transitivity; apply Id.map;
      symmetry; apply Nat.assoc 1 m 1; symmetry; apply Nat.assoc;
      apply Id.map (λ k, n + k + 1); apply Nat.comm; apply le.leSucc
    end)

  -- ℕ-specific property
  hott def dist.max : Π (n m : ℕ), dist n m ≤ max n m
  | Nat.zero,   Nat.zero   => idp 0
  | Nat.succ n, Nat.zero   => max.refl _
  | Nat.zero,   Nat.succ m => max.refl _
  | Nat.succ n, Nat.succ m => le.trans (max n m) (le.leSucc _)

  hott def dist.le (n m : ℕ) : le (dist n m) (n + m) :=
  le.trans (dist.max n m) (max.leAdd n m)

  hott def dist.translation (n m : ℕ) : Π k, dist n m = dist (n + k) (m + k)
  | Nat.zero   => idp _
  | Nat.succ k => translation n m k
end Nat

namespace UnitList
  universe u

  def zero' : List 𝟏 := []
  def succ' : List 𝟏 → List 𝟏 := List.cons ★

  def ind' {E : List 𝟏 → Type u} (e₀ : E zero') (eₛ : Π (n : List 𝟏), E n → E (succ' n)) : Π n, E n
  | []      => e₀
  | ★ :: xs => eₛ xs (ind' e₀ eₛ xs)

  def encode : ℕ → List 𝟏
  | Nat.zero   => zero'
  | Nat.succ n => succ' (encode n)

  def decode : List 𝟏 → ℕ
  | []      => Nat.zero
  | _ :: xs => Nat.succ (decode xs)

  def decodeEncode : Π n, decode (encode n) = n
  | Nat.zero   => idp _
  | Nat.succ n => Id.map Nat.succ (decodeEncode n)

  def encodeDecode : Π xs, encode (decode xs) = xs
  | []      => idp _
  | ★ :: xs => Id.map succ' (encodeDecode xs)

  hott def iso : ℕ ≃ List 𝟏 :=
  ⟨encode, (⟨decode, decodeEncode⟩, ⟨decode, encodeDecode⟩)⟩

  noncomputable hott def equality : ℕ = List 𝟏 := ua iso
end UnitList

end Theorems
end GroundZero