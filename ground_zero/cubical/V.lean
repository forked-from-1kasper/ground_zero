import ground_zero.cubical.path ground_zero.theorems.ua
open ground_zero.HITs ground_zero.types

namespace ground_zero.cubical
universes u v

def V (i : I) {α β : Sort u} (e : α ≃ β) : Sort u :=
interval.rec α β (ground_zero.ua e) i

def Vin (i : I) {α β : Sort u} (e : α ≃ β) (m : α) : V i e :=
interval.hrec (λ i, V i e) m (e.fst m) (begin
  symmetry, transitivity, apply heq.inclusion,
  exact (ground_zero.ua.transport_rule e m)⁻¹,
  symmetry, apply heq.eq_subst_heq (ground_zero.ua e)
end) i

-- why it isn’t need to be marked as noncomputable??
def ua {α β : Sort u} (e : α ≃ β) : α ⇝ β := <i> V i e

def iso_to_path {α β : Sort u} (f : α → β) (g : β → α)
  (F : f ∘ g ~ id) (G : g ∘ f ~ id) : α ⇝ β :=
ua ⟨f, ground_zero.types.qinv.q2b f ⟨g, ⟨F, G⟩⟩⟩

end ground_zero.cubical