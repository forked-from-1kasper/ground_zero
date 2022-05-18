import ground_zero.cubical.path ground_zero.theorems.ua
open ground_zero.HITs ground_zero.types

/-
  V, Vproj
  * https://arxiv.org/abs/1712.01800
    Part 6 ‘Rules’, page 66 ‘Univalence’
  
  ua, uabeta
-/

namespace ground_zero.cubical
universes u v

@[hott] def V (i : I) {A B : Type u} (e : A ≃ B) : Type u :=
interval.rec A B (ground_zero.ua e) i

@[hott] noncomputable def Vproj (i : I) {A B : Type u} (e : A ≃ B) (m : A) : V i e :=
@interval.ind (λ i, V i e) m (e.fst m) (begin
  apply Id.trans,
  apply interval.transportconst_with_seg,
  apply ground_zero.ua.comp_rule
end) i

@[hott] def ua {A B : Type u} (e : A ≃ B) : Path Type* A B := <i> V i e

@[hott] noncomputable def uabeta {A B : Type u} (e : A ≃ B) (m : A) :
  Path B (coe⁻¹ 0 1 (λ i, V i e) m) (e.1 m) :=
<i> coe⁻¹ i 1 (λ i, V i e) (Vproj i e m)

@[hott] def univalence.elim {A B : Type u} (p : Path Type* A B) : A ≃ B :=
Path.coe 0 1 (λ i, A ≃ p # i) (equiv.id A)

@[hott] noncomputable def univalence.beta {A B : Type u} (e : A ≃ B) (m : A) :
  Path B (trans⁻¹ (ua e) m) (e.1 m) :=
<i> coe⁻¹ i 1 (λ i, ua e # i) (Vproj i e m)

@[hott] def iso {A B : Type u} (f : A → B) (g : B → A)
  (F : f ∘ g ~' id) (G : g ∘ f ~' id) : Path Type* A B :=
ua ⟨f, ground_zero.types.qinv.to_biinv f
  ⟨g, ⟨Path.homotopy_equality F, Path.homotopy_equality G⟩⟩⟩

@[hott] def neg_neg (x : I) : Path I (Path.neg (Path.neg x)) x :=
(Path.conn_and Path.seg⁻¹ (Path.neg x))⁻¹ ⬝ Path.interval_contr_right x

@[hott] def twist : Path Type I I :=
iso Path.neg Path.neg neg_neg neg_neg

end ground_zero.cubical