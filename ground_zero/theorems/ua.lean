import ground_zero.structures
open ground_zero.types.equiv (idtoeqv homotopy)
open ground_zero.types.equiv (renaming id -> ideqv)
open ground_zero.types
open ground_zero.structures ground_zero.types.not

/-
  Univalence axiom formulated using equivalence J-rule.

  ua, idtoeqv, comp_rule, prop_uniq
  * HoTT 2.10

  Full univalence: (α ≃ β) ≃ (α = β).

  Proof that Type is not a set.
  * HoTT 3.1, example 3.1.9
-/

namespace ground_zero

hott theory

universes u v u' v'

axiom J {π : Π (α β : Type u), α ≃ β → Type v}
  (h : Π (α : Type u), π α α (ideqv α))
  {α β : Type u} (e : α ≃ β) : π α β e
axiom Jβrule {π : Π (α β : Type u), α ≃ β → Type v}
  {h : Π (α : Type u), π α α (ideqv α)} {α : Type u} :
  J h (ideqv α) = h α :> π α α (ideqv α)

noncomputable abbreviation Jrule
  (π : Π (α β : Type u), α ≃ β → Type v)
  (h : Π (α : Type u), π α α (ideqv α))
  {α β : Type u} (e : α ≃ β) : π α β e :=
J h e

noncomputable def ua {α β : Type u} : α ≃ β → α = β :=
J idp

namespace ua

@[hott] noncomputable def refl_on_ua (α : Type u) :
  ua (ideqv α) = idp α :=
by apply Jβrule

@[hott] noncomputable def comp_rule {α β : Type u} (e : α ≃ β) :
  Π (x : α), x =[ua e] e.fst x :=
begin
  refine J _ e, intros ψ x,
  refine types.Id.rec _ (refl_on_ua ψ)⁻¹,
  reflexivity
end

@[hott] noncomputable def transport_rule {α β : Type u} (e : α ≃ β) :
  Π (x : α), types.equiv.subst (ua e) x = e.fst x :=
begin
  refine J _ e, intros ψ x,
  refine types.Id.rec _ (refl_on_ua ψ)⁻¹,
  reflexivity
end

@[hott] noncomputable def transportconst_rule {α β : Type u} (e : α ≃ β) :
  Π (x : α), equiv.transportconst (ua e) x = e.fst x :=
begin
  fapply ground_zero.J _ e, intros α x,
  transitivity, apply Id.map (λ p, equiv.transportconst p x),
  apply refl_on_ua, reflexivity
end

@[hott] noncomputable def transportconst_inv_rule {α β : Type u} (e : α ≃ β) :
  Π (x : β), equiv.transportconst_inv (ua e) x = e.left x :=
begin
  fapply ground_zero.J _ e, intros α x,
  transitivity, apply Id.map (λ p, equiv.transportconst_inv p x),
  apply refl_on_ua, reflexivity
end

@[hott] noncomputable def transport_inv_rule {α β : Type u} (e : α ≃ β) :
  Π (x : β), types.equiv.subst_inv (ua e) x = e.left x :=
begin
  refine J _ e, intros ψ x,
  refine types.Id.rec _ (refl_on_ua ψ)⁻¹,
  reflexivity
end

@[hott] def idtoeqv_and_id {α : Type u} :
  idtoeqv (idp α) = ideqv α :=
by trivial

@[hott] noncomputable def uaβrule {α β : Type u} (e : α ≃ β) :
  idtoeqv (ua e) = e := begin
  refine J _ e, intro δ, change _ = idtoeqv (idp δ),
  apply Id.map idtoeqv, apply Jβrule
end

@[hott] noncomputable def prop_uniq {α β : Type u} (p : α = β) :
  ua (idtoeqv p) = p :=
begin induction p, exact Jβrule end

@[hott] noncomputable def univalence (α β : Type u) :
  (α ≃ β) ≃ (α = β) :=
⟨ua, (⟨idtoeqv, uaβrule⟩, ⟨idtoeqv, prop_uniq⟩)⟩

@[hott] noncomputable def propext {α β : Type u}
  (F : prop α) (G : prop β) : (α ↔ β) → α = β :=
λ h, ua (prop_equiv_lemma F G h.left h.right)

@[hott] noncomputable def ua_trans :
  Π {α β : Type u} (p : α ≃ β) {γ : Type u} (q : β ≃ γ),
    ua (equiv.trans p q) = ua p ⬝ ua q :=
begin
  fapply @J (λ α β (p : α ≃ β), Π {γ : Type u} (q : β ≃ γ),
    ua (equiv.trans p q) = ua p ⬝ ua q),
  fapply J, intro δ, symmetry, transitivity,
  apply Id.map, apply refl_on_ua,
  apply types.Id.refl_right
end

@[hott] def is_zero : ℕ → bool
|    0    := tt
| (_ + 1) := ff

@[hott] example (h : 0 = 1) : 𝟎 :=
ff_neq_tt (is_zero # h)⁻¹

@[hott] def succ_neq_zero {n : ℕ} : ¬(nat.succ n = 0) :=
λ h, ff_neq_tt (is_zero # h)

@[hott] def neg_bool_equiv : bool ≃ bool :=
begin existsi bnot, split; existsi bnot; intro x; induction x; trivial end

@[hott] noncomputable def coproduct_set {α β : Type}
  (f : hset α) (g : hset β) : hset (α + β)
| (coproduct.inl x) (coproduct.inl y) :=
  transport structures.prop (ua $ @coproduct.inl.inj' α β x y)⁻¹ f
| (coproduct.inl x) (coproduct.inr y) :=
  transport structures.prop (ua $ @types.coproduct.inl.inl_inr α β x y)⁻¹
            structures.empty_is_prop
| (coproduct.inr x) (coproduct.inl y) :=
  transport structures.prop (ua $ @types.coproduct.inr.inr_inl α β x y)⁻¹
            structures.empty_is_prop
| (coproduct.inr x) (coproduct.inr y) :=
  transport structures.prop (ua $ @coproduct.inr.inj' α β x y)⁻¹ g

@[hott] noncomputable def universe_not_a_set : ¬(hset Type) :=
begin
  intro error,
  let p : bool = bool := ua neg_bool_equiv,
  let h := transport proto.idfun p tt,
  let g : h = ff := transport_rule neg_bool_equiv tt,
  let oops : h = tt :=
    (λ p, transport proto.idfun p tt) #
      (error p (idp bool)),
  let uh_oh : ff = tt := g⁻¹ ⬝ oops,
  apply ff_neq_tt, exact uh_oh
end

-- exercise 2.17 (i) in HoTT book
@[hott] noncomputable def product_equiv₁ {α α' β β' : Type u}
  (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') :=
begin
  have p := ua e₁, have q := ua e₂,
  induction p, induction q, reflexivity
end

@[hott] noncomputable def product_equiv₂ {α α' β β' : Type u}
  (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') :=
begin
  refine J _ e₁, intro A,
  refine J _ e₂, intro B,
  reflexivity
end

section
  open ground_zero.types.product
  @[hott] def product_equiv₃ {α : Type u} {α' : Type v} {β : Type u'} {β' : Type v'}
    (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') :=
  begin
    existsi (bimap e₁.forward e₂.forward), split,
    { existsi (bimap e₁.left e₂.left), intro x,
      induction x with a b, apply construction,
      apply e₁.left_forward, apply e₂.left_forward },
    { existsi (bimap e₁.right e₂.right), intro x,
      induction x with a b, apply construction,
      apply e₁.forward_right, apply e₂.forward_right }
  end
end

@[hott] def family_on_bool {π : bool → Type u} :
  (π ff × π tt) ≃ Π (b : bool), π b := begin
  let construct : (π ff × π tt) → Π (b : bool), π b :=
  begin
    intros x b, cases x with p q,
    cases b, exact p, exact q
  end,
  let deconstruct : (Π (b : bool), π b) → (π ff × π tt) :=
  begin intro H, split, exact H ff, exact H tt end,
  existsi construct, split; existsi deconstruct,
  { intro x, cases x with p q, reflexivity },
  { intro x, apply theorems.funext,
    intro b, induction b,
    repeat { reflexivity } }
end

end ua
end ground_zero