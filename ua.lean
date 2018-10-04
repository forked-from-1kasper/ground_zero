import ground_zero.equiv
open ground_zero.equiv (idtoeqv)

namespace ground_zero.ua

universe u
axiom ua {α β : Type u} : α ≃ β → α = β

axiom comp_rule₁ {α β : Type u} (e : α ≃ β) : (idtoeqv (ua e)) = e
axiom comp_rule₂ {α β : Type u} (p : α = β) : (ua (idtoeqv p)) = p

end ground_zero.ua