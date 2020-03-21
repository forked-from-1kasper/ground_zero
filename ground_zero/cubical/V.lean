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

@[hott] def V (i : I) {α β : Type u} (e : α ≃ β) : Type u :=
interval.rec α β (ground_zero.ua e) i

@[hott] noncomputable def Vproj (i : I) {α β : Type u} (e : α ≃ β) (m : α) : V i e :=
@interval.ind (λ i, V i e) m (e.fst m) (begin
  apply ground_zero.types.eq.trans,
  apply interval.transportconst_with_seg,
  apply ground_zero.ua.comp_rule
end) i

@[hott] def ua {α β : Type u} (e : α ≃ β) : α ⇝ β := <i> V i e

@[hott] noncomputable def uabeta {α β : Type u} (e : α ≃ β) (m : α) :
  coe⁻¹ 0 1 (λ i, V i e) m ⇝ e.fst m :=
<i> coe⁻¹ i 1 (λ i, V i e) (Vproj i e m)

@[hott] def univalence.formation (α β : Type u) :=
α ≃ β → α ⇝ β

@[hott] def univalence.intro {α β : Type u} : univalence.formation α β := ua

@[hott] def univalence.elim {α β : Type u} (p : α ⇝ β) : α ≃ β :=
Path.coe 0 1 (λ i, α ≃ p # i) (equiv.id α)

@[hott] noncomputable def univalence.beta {α β : Type u} (e : α ≃ β) (m : α) :
  trans⁻¹ (ua e) m ⇝ e.fst m :=
<i> coe⁻¹ i 1 (λ i, ua e # i) (Vproj i e m)

@[hott] def iso {α β : Type u} (f : α → β) (g : β → α)
  (F : f ∘ g ~' id) (G : g ∘ f ~' id) : α ⇝ β :=
ua ⟨f, ground_zero.types.qinv.q2b f
  ⟨g, ⟨Path.homotopy_equality F, Path.homotopy_equality G⟩⟩⟩

@[hott] def twist : I ⇝ I :=
iso Path.neg Path.neg Path.neg_neg Path.neg_neg

end ground_zero.cubical