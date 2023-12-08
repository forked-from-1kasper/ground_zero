import GroundZero.Theorems.Univalence
import GroundZero.Cubical.Path

open GroundZero.HITs.Interval (transportconstWithSeg)
open GroundZero GroundZero.HITs GroundZero.Types

/-
  V, Vproj
  * https://arxiv.org/abs/1712.01800
    Part 6 ‘Rules’, page 66 ‘Univalence’

  ua, uabeta
-/

namespace GroundZero.Cubical
universe u v

hott definition V (i : I) {A B : Type u} (e : A ≃ B) : Type u :=
Interval.rec A B (ua e) i

hott definition Vproj (i : I) {A B : Type u} (e : A ≃ B) (m : A) : V i e :=
@Interval.ind (λ i, V i e) m (e m) (transportconstWithSeg (ua e) m ⬝ uaβ e m) i

hott definition ua {A B : Type u} (e : A ≃ B) : Path (Type u) A B := <i> V i e

hott definition uabeta {A B : Type u} (e : A ≃ B) (m : A) :
  Path B (coe⁻¹ 0 1 (λ i, V i e) m) (e.1 m) :=
<i> coe⁻¹ i 1 (λ i, V i e) (Vproj i e m)

hott definition univalence.elim {A B : Type u} (p : Path (Type u) A B) : A ≃ B :=
Path.coe 0 1 (λ i, A ≃ p @ i) (Equiv.ideqv A)

hott definition iso {A B : Type u} (f : A → B) (g : B → A)
  (F : f ∘ g ~′ id) (G : g ∘ f ~′ id) : Path (Type u) A B :=
ua ⟨f, Qinv.toBiinv f ⟨g, ⟨Path.homotopyEquality F, Path.homotopyEquality G⟩⟩⟩

end GroundZero.Cubical
