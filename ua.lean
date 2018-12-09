import ground_zero.product
open ground_zero.equiv (idtoeqv) ground_zero.not
open ground_zero.equiv (homotopy)
open ground_zero.structures


namespace ground_zero

local infix ` = ` := eq
universes u v

axiom J {π : Π (α β : Sort u), α ≃ β → Sort v}
  (h : Π (α : Sort u), π α α (equiv.id α))
  {α β : Sort u} (e : α ≃ β) : π α β e
axiom Jβrule {π : Π (α β : Sort u), α ≃ β → Sort v}
  {h : Π (α : Sort u), π α α (equiv.id α)} {α : Sort u} :
  J h (equiv.id α) = h α :> π α α (equiv.id α)

noncomputable def ua {α β : Sort u} : α ≃ β → α = β :=
J eq.refl

namespace ua

noncomputable theorem comp_rule {α β : Sort u} (e : α ≃ β) :
  Π (x : α), x =[ua e] e.fst x :=
begin
  refine J _ e, intros γ x, simp [ua], transitivity,
  apply eq.map (λ p, equiv.transport functions.idfun p x),
  exact Jβrule, reflexivity
end

noncomputable theorem refl_on_ua {α : Sort u} :
  ua (equiv.id α) = eq.refl α :=
begin unfold ua, exact Jβrule end

theorem idtoeqv_and_id {α : Sort u} :
  idtoeqv (eq.refl α) = equiv.id α :=
begin simp [idtoeqv] end

noncomputable theorem prop_uniq {α β : Sort u} (p : α = β) :
  (ua (idtoeqv p)) = p := begin
  unfold ua, induction p, exact Jβrule
end

noncomputable theorem univalence (α β : Sort u) :
  (α ≃ β) ≃ (α = β) := begin
  existsi ua, split; existsi idtoeqv,
  { intro e, simp,
    refine J _ e,
    intro δ, simp [ua], transitivity,
    exact idtoeqv # Jβrule, reflexivity },
  { intro e, simp, apply prop_uniq }
end

def bool_to_universe : bool → Type
| tt := ground_zero.unit
| ff := empty

theorem ff_neq_tt (h : ff = tt) : empty :=
@ground_zero.eq.rec
  bool tt (λ b _, bool_to_universe b)
  ground_zero.unit.star ff h⁻¹

noncomputable theorem universe_not_a_set : ¬(hset Type) :=
begin
  intro error,
  let e : bool ≃ bool := begin
    existsi bnot,
    split; existsi bnot; intro x; simp
  end,
  let p : bool = bool := ua e,
  let h₁ := equiv.transport functions.idfun p tt,
  let h₂ :=
    equiv.transport functions.idfun
    (ground_zero.eq.refl bool) tt,
  let g₁ : h₁ = ff := comp_rule e tt,
  let g₂ : h₂ = tt := by reflexivity,
  let oops : h₁ = h₂ :=
    (λ p, ground_zero.equiv.transport functions.idfun p tt) #
    (@hset.intro Type error bool bool
                 p (ground_zero.eq.refl bool)),
  let uh_oh := g₁⁻¹ ⬝ oops ⬝ g₂,
  apply ff_neq_tt, apply uh_oh
end

-- exercise 2.17 (i) in HoTT book
noncomputable theorem product_equiv₁ {α α' β β' : Sort u}
  (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') := begin
  have p := ua e₁, have q := ua e₂,
  induction p, induction q,
  reflexivity
end

noncomputable theorem product_equiv₂ {α α' β β' : Sort u}
  (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') :=
begin
  refine J _ e₁, intro δ,
  refine J _ e₂, intro σ,
  reflexivity
end

theorem product_equiv₃ {α α' β β' : Sort u}
  (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') := begin
  cases e₁ with f H, cases H with linv rinv,
  cases linv with g α₁, cases rinv with h β₁,

  cases e₂ with f' H, cases H with linv' rinv',
  cases linv' with g' α₂, cases rinv' with h' β₂,

  existsi (product.bimap f f'), split,
  { existsi (product.bimap g g'), intro x,
    cases x with u v, simp [*],
    apply product.construction,
    exact α₁ u, exact α₂ v },
  { existsi (product.bimap h h'), intro x,
    cases x with u v, simp [*],
    apply product.construction,
    exact β₁ u, exact β₂ v }
end

end ua
end ground_zero