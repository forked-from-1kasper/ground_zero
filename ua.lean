import ground_zero.equiv ground_zero.eq 
import ground_zero.structures ground_zero.unit
import ground_zero.support
open ground_zero.equiv (idtoeqv) ground_zero.not
open ground_zero.equiv (homotopy)
open ground_zero.structures

namespace ground_zero

universes u v

axiom J {π : Π (α β : Sort u), α ≃ β → Sort v}
  (h : Π (α : Sort u), π α α (equiv.id α)) :
  Π (α β : Sort u) (e : α ≃ β), π α β e
axiom Jβrule {π : Π (α β : Sort u), α ≃ β → Sort v}
  {h : Π (α : Sort u), π α α (equiv.id α)} {α : Sort u} :
  J h α α (equiv.id α) = h α :> π α α (equiv.id α)

noncomputable def ua {α β : Sort u} : α ≃ β → α = β :> Sort u :=
J eq.refl α β

--axiom ua {α β : Sort u} : (α ≃ β) → (α = β :> Sort u)

namespace ua

noncomputable theorem comp_rule {α β : Sort u} (e : α ≃ β) :
  Π (x : α),
  ground_zero.equiv.transport (ua e) x = e.fst x :> _ :=
begin
  refine @J
    (λ α β e, Π (x : α),
      ground_zero.equiv.transport (ua e) x = e.fst x :> _)
    _ α β e,
  intros δ u, simp [ua],
  rw [support.truncation Jβrule],
  simp [equiv.transport], simp [idtoeqv]
end

theorem idtoeqv_and_id {α : Sort u} :
  idtoeqv (eq.refl α) = equiv.id α :> α ≃ α :=
begin simp [idtoeqv] end

theorem prop_uniq {α β : Sort u} (p : α = β :> Sort u) :
  (ua (idtoeqv p)) = p :> _ := begin
  simp [ua], induction p,
  rw [support.truncation idtoeqv_and_id],
  rw [support.truncation Jβrule]
end

noncomputable theorem univalence (α β : Sort u) :
  (α ≃ β) ≃ (α = β :> Sort u) := begin
  existsi ua, split; existsi idtoeqv,
  { intro e, simp,
    refine J _ α β e,
    intro δ, simp [ua],
    rw [support.truncation Jβrule],
    trivial },
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

end ua
end ground_zero