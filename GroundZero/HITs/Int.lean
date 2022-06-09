import GroundZero.Theorems.Nat
open GroundZero.Types
open GroundZero

/-
  Integers ℤ as a quotient of ℕ × ℕ.
  * HoTT 6.10, remark 6.10.7
-/

namespace GroundZero.HITs

hott def Int.rel (w₁ w₂ : ℕ × ℕ) : Type :=
w₁.1 + w₂.2 = w₁.2 + w₂.1

hott def Int := Graph Int.rel
local notation "ℤ" => Int

namespace Nat.Product
  def add (x y : ℕ × ℕ) : ℕ × ℕ :=
  (x.1 + y.1, x.2 + y.2)

  instance : Add (ℕ × ℕ) := ⟨add⟩

  def mul (x y : ℕ × ℕ) : ℕ × ℕ :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)

  instance : Mul (ℕ × ℕ) := ⟨mul⟩
end Nat.Product

namespace Int
  universe u v

  def mk : ℕ × ℕ → ℤ := Graph.elem
  def elem (a b : ℕ) : ℤ := Graph.elem (a, b)

  def pos (n : ℕ) := mk (n, 0)
  instance (n : ℕ) : OfNat ℤ n := ⟨pos n⟩

  def neg (n : ℕ) := mk (0, n)

  hott def glue {a b c d : ℕ} (H : a + d = b + c) : mk (a, b) = mk (c, d) :=
  Graph.line H

  hott def ind {C : ℤ → Type u} (mkπ : Π x, C (mk x))
    (glueπ : Π {a b c d : ℕ} (H : a + d = b + c),
      mkπ (a, b) =[glue H] mkπ (c, d)) (x : ℤ) : C x :=
  begin fapply Graph.ind; exact mkπ; intros x y H; apply glueπ end

  hott def rec {C : Type u} (mkπ : ℕ × ℕ → C)
    (glueπ : Π {a b c d : ℕ} (H : a + d = b + c),
      mkπ (a, b) = mkπ (c, d)) : ℤ → C :=
  begin fapply Graph.rec; exact mkπ; intros x y H; apply glueπ H end

  instance : Neg Int :=
  ⟨rec (λ x, mk ⟨x.2, x.1⟩) (λ H, glue H⁻¹)⟩

  hott def addRight (a b k : ℕ) : mk (a, b) = mk (a + k, b + k) :=
  begin
    apply glue; transitivity; symmetry; apply Theorems.Nat.assoc;
    symmetry; transitivity; symmetry; apply Theorems.Nat.assoc;
    apply Id.map (λ n, n + k); apply Theorems.Nat.comm
  end

end Int
end GroundZero.HITs