import GroundZero.HITs.Sphere
open GroundZero.HITs

universe u v

namespace GroundZero
namespace Types

-- https://github.com/leanprover/lean2/blob/master/hott/homotopy/cellcomplex.hlean
-- https://arxiv.org/abs/1802.02191

hott definition Model :=
Σ (X : Type u), X → Type v

hott definition FdCC : ℕ → Model
| Nat.zero   => ⟨Set u, Sigma.fst⟩
| Nat.succ n => ⟨Σ (X : (FdCC n).1) (A : Set u), A.1 × Sⁿ → (FdCC n).2 X,
                 λ w, Pushout (@Prod.fst w.2.1.1 Sⁿ) w.2.2⟩

-- finite-dimensional cell complex
hott definition fdcc (n : ℕ) := (FdCC n).1

-- and its homotopy type (i.e. ∞-groupoid)
hott definition fdcc.ωGroupoid {n : ℕ} (X : fdcc n) := (FdCC n).2 X
notation "Πω" => fdcc.ωGroupoid

end Types
end GroundZero
