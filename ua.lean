import ground_zero.equiv ground_zero.eq ground_zero.equiv
import ground_zero.structures ground_zero.unit
open ground_zero.equiv (idtoeqv) ground_zero.not
open ground_zero.equiv (homotopy)
open ground_zero.structures

namespace ground_zero.ua

universe u
axiom ua {α β : Type u} : α ≃ β → α = β

axiom comp_rule {α β : Type u} (e : α ≃ β) (x : α) :
  ground_zero.equiv.transport (ua e) x = e.fst x
axiom prop_uniq {α β : Type u} (p : α = β) : (ua (idtoeqv p)) = p

def bool_to_universe : bool → Type
| tt := ground_zero.unit
| ff := empty

theorem ff_neq_tt (h : ff = tt) : empty :=
@eq.rec bool tt bool_to_universe ground_zero.unit.star ff (eq.symm h)

-- lol
theorem univalence_Lean_fail : empty := begin
  let e : bool ≃ bool :=
  begin existsi bnot, split; existsi bnot; simp [homotopy] end,
  let p : bool = bool := ua e,
  let h₁ := ground_zero.equiv.transport p tt,
  let h₂ := ground_zero.equiv.transport p tt,
  let g₁ : h₁ = ff := comp_rule e tt,
  let g₂ : h₂ = tt := eq.refl tt,
  let oops : h₁ = h₂ := by trivial,
  let uh_oh := eq.trans (eq.trans (eq.symm g₁) oops) g₂,
  apply ff_neq_tt, apply uh_oh
end

#reduce univalence_Lean_fail

end ground_zero.ua