import ground_zero.types.rational

namespace ground_zero
namespace types

structure dedekind.is_cut (L U : ℚ → Prop) :=
(inhabited : (∃ q, L q) ∧ ∃ r, U r)
(rounded : ∀ q, iff (L q) (∃ r, q < r ∧ L r) ∧
           ∀ r, iff (U r) (∃ q, q < r ∧ U q))
(disjoint : ∀ q, ¬(L q ∧ U q))
(located : ∀ q r, q < r → L q ∨ U r)

def dedekind : Type := Σ L U, dedekind.is_cut L U
notation `ℝ` := dedekind

namespace dedekind
  namespace rat
    def L (q r : ℚ) : Prop := r < q
    def U (q r : ℚ) : Prop := q < r
  end rat
end dedekind

end types
end ground_zero