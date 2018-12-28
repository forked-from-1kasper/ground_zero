import ground_zero.cubical.path ground_zero.theorems.ua
open ground_zero.HITs

namespace ground_zero.cubical
universes u v

def V (i : I) {α β : Sort u} (e : α ≃ β) : Sort u :=
interval.rec α β (ground_zero.ua e) i

-- why it isn’t need to be marked as noncomputable??
def ua {α β : Sort u} (e : α ≃ β) : α ⇝ β := <i> V i e

end ground_zero.cubical