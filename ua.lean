import ground_zero.equiv ground_zero.eq 
import ground_zero.structures ground_zero.unit
open ground_zero.equiv (idtoeqv) ground_zero.not
open ground_zero.equiv (homotopy)
open ground_zero.structures

universe u
axiom ua {α β : Sort u} : (α ≃ β) → (α = β :> Sort u)

namespace ground_zero.ua

axiom comp_rule {α β : Sort u} (e : α ≃ β) (x : α) :
  ground_zero.equiv.transport (ua e) x = e.fst x :> _
axiom prop_uniq {α β : Sort u} (p : α = β :> Sort u) :
  (ua (idtoeqv p)) = p :> _

noncomputable theorem univalence (α β : Sort u) :
  (α ≃ β) ≃ (α = β :> Sort u) := begin
  existsi ua, split; existsi idtoeqv,
  { intro e, simp,
    have g := comp_rule e,
    admit },
  { intro e, simp, apply prop_uniq }
end

def bool_to_universe : bool → Type
| tt := ground_zero.unit
| ff := empty

theorem ff_neq_tt (h : ff = tt :> bool) : empty :=
@ground_zero.eq.rec
  bool tt (λ b _, bool_to_universe b)
  ground_zero.unit.star ff h⁻¹

noncomputable theorem universe_not_a_set : ¬(hset Type) :=
begin
  intro error,
  let e : bool ≃ bool := begin
    existsi bnot, split; existsi bnot;
    simp [homotopy]; intro x; simp
  end,
  let p : bool = bool :> Type := ua e,
  let h₁ := ground_zero.equiv.transport p tt,
  let h₂ :=
    ground_zero.equiv.transport
    (ground_zero.eq.refl bool) tt,
  let g₁ : h₁ = ff :> _ := comp_rule e tt,
  let g₂ : h₂ = tt :> _ := by reflexivity,
  let oops : h₁ = h₂ :> _ :=
    (λ p, ground_zero.equiv.transport p tt) #
    (@hset.intro Type error bool bool
                 p (ground_zero.eq.refl bool)),
  let uh_oh := g₁⁻¹ ⬝ oops ⬝ g₂,
  apply ff_neq_tt, apply uh_oh
end

end ground_zero.ua