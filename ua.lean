import ground_zero.equiv ground_zero.eq ground_zero.equiv
open ground_zero.equiv (idtoeqv) ground_zero.not
open ground_zero.equiv (homotopy)

namespace ground_zero.ua

universe u
axiom ua {α β : Type u} : α ≃ β → α = β

axiom comp_rule₁ {α β : Type u} (e : α ≃ β) : (idtoeqv (ua e)) = e
axiom comp_rule₂ {α β : Type u} (p : α = β) : (ua (idtoeqv p)) = p

theorem not_set : ¬(set (Type u)) := begin
  assume inst,
  let e : bool ≃ bool :=
  begin existsi bnot, split; existsi bnot; simp [homotopy] end,
  admit
end

end ground_zero.ua