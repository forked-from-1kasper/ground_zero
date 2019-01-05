import ground_zero.cubical.path ground_zero.theorems.ua
open ground_zero.HITs ground_zero.types

/-
  V, Vproj
  * https://arxiv.org/abs/1712.01800
    Part 6 ‘Rules’, page 66 ‘Univalence’
-/

namespace ground_zero.cubical
universes u v

def V (i : I) {α β : Sort u} (e : α ≃ β) : Sort u :=
interval.rec α β (ground_zero.ua e) i

def Vproj (i : I) {α β : Sort u} (e : α ≃ β) (m : α) : V i e :=
interval.hrec (λ i, V i e) m (e.fst m) (begin
  symmetry, transitivity, apply heq.inclusion,
  exact (ground_zero.ua.transport_rule e m)⁻¹,
  symmetry, apply heq.eq_subst_heq (ground_zero.ua e)
end) i

-- why it isn’t need to be marked as noncomputable??
def ua {α β : Sort u} (e : α ≃ β) : α ⇝ β := <i> V i e

def uabeta {α β : Sort u} (e : α ≃ β) (m : α) :
  Path.coe_inv 0 1 (λ i, V i e) m ⇝ (e.fst m) :=
<i> Path.coe_inv i 1 (λ i, V i e) (Vproj i e m)

def univalence.formation (α β : Sort u) :=
α ≃ β → α ⇝ β

def univalence.intro {α β : Sort u} : univalence.formation α β := ua

def univalence.elim {α β : Sort u} (p : α ⇝ β) : α ≃ β :=
Path.coe 0 1 (λ i, α ≃ p # i) (equiv.id α)

def iso {α β : Sort u} (f : α → β) (g : β → α)
  (F : f ∘ g ~ id) (G : g ∘ f ~ id) : α ⇝ β :=
ua ⟨f, ground_zero.types.qinv.q2b f ⟨g, ⟨F, G⟩⟩⟩

end ground_zero.cubical