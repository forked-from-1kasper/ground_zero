import GroundZero.Cubical.Path
import GroundZero.Theorems.UA
open GroundZero GroundZero.HITs GroundZero.Types

/-
  V, Vproj
  * https://arxiv.org/abs/1712.01800
    Part 6 ‘Rules’, page 66 ‘Univalence’
  
  ua, uabeta
-/

namespace GroundZero.Cubical
universe u v

hott def V (i : I) {A B : Type u} (e : A ≃ B) : Type u :=
Interval.rec A B (GroundZero.ua e) i

noncomputable hott def Vproj (i : I) {A B : Type u} (e : A ≃ B) (m : A) : V i e :=
@Interval.ind (λ i, V i e) m (e m) (begin
  apply Id.trans;
  apply Interval.transportconstWithSeg (GroundZero.ua e);
  apply ua.compRule
end) i

hott def ua {A B : Type u} (e : A ≃ B) : Path (Type u) A B := <i> V i e

noncomputable hott def uabeta {A B : Type u} (e : A ≃ B) (m : A) :
  Path B (coe⁻¹ 0 1 (λ i, V i e) m) (e.1 m) :=
<i> coe⁻¹ i 1 (λ i, V i e) (Vproj i e m)

hott def univalence.elim {A B : Type u} (p : Path (Type u) A B) : A ≃ B :=
Path.coe 0 1 (λ i, A ≃ p @ i) (Equiv.ideqv A)

noncomputable hott def univalence.beta {A B : Type u} (e : A ≃ B) (m : A) :
  Path B (trans⁻¹ (ua e) m) (e.1 m) :=
<i> coe⁻¹ i 1 (λ i, (ua e) @ i) (Vproj i e m)

hott def iso {A B : Type u} (f : A → B) (g : B → A)
  (F : f ∘ g ~′ id) (G : g ∘ f ~′ id) : Path (Type u) A B :=
ua ⟨f, Qinv.toBiinv f ⟨g, ⟨Path.homotopyEquality F, Path.homotopyEquality G⟩⟩⟩

hott def negNeg (x : I) : Path I (Path.neg (Path.neg x)) x :=
Path.com (Path.symm (Path.connAnd (Path.symm Path.seg) (Path.neg x))) (Path.intervalContrRight x)

hott def twist : Path Type I I :=
iso Path.neg Path.neg negNeg negNeg

end GroundZero.Cubical