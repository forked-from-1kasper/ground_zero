import GroundZero.HITs.Sphere
open GroundZero.HITs

universe u v w

namespace GroundZero
namespace Types

/- https://github.com/leanprover/lean2/blob/master/hott/homotopy/cellcomplex.hlean
   Cellular Cohomology in Homotopy Type Theory, https://arxiv.org/abs/1802.02191
-/

hott definition Model :=
Σ (X : Type u), X → Type v

hott definition FdCC : ℕ → Model
| Nat.zero   => ⟨Set u, Sigma.pr₁⟩
| Nat.succ n => ⟨Σ (X : (FdCC n).1) (A : Set u), A.1 × Sⁿ → (FdCC n).2 X, λ w, Pushout Prod.pr₁ w.2.2⟩

-- finite-dimensional cell complex
hott definition fdcc (n : ℕ) := (FdCC n).1

-- and its homotopy type (i.e. ∞-groupoid)
hott definition fdcc.ωGroupoid {n : ℕ} (X : fdcc n) := (FdCC n).2 X
notation "Πω" => fdcc.ωGroupoid

end Types
end GroundZero
