import ground_zero.types.product ground_zero.structures
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

universes u v

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

@[hott] noncomputable theorem refl_on_ua (α : Type u) :
  ua (ideqv α) = idp α :=
by apply Jβrule

@[hott] noncomputable theorem comp_rule {α β : Type u} (e : α ≃ β) :
  Π (x : α), x =[ua e] e.fst x := begin
  refine J _ e, intros ψ x,
  refine types.eq.rec _ (refl_on_ua ψ)⁻¹,
  reflexivity
end

@[hott] noncomputable theorem transport_rule {α β : Type u} (e : α ≃ β) :
  Π (x : α), types.equiv.subst (ua e) x = e.fst x := begin
  refine J _ e, intros ψ x,
  refine types.eq.rec _ (refl_on_ua ψ)⁻¹,
  reflexivity
end

@[hott] noncomputable theorem transport_inv_rule {α β : Type u} (e : α ≃ β) :
  Π (x : β), types.equiv.subst_inv (ua e) x = e.backward x := begin
  refine J _ e, intros ψ x,
  refine types.eq.rec _ (refl_on_ua ψ)⁻¹,
  reflexivity
end

@[hott] theorem idtoeqv_and_id {α : Type u} :
  idtoeqv (idp α) = ideqv α :=
by trivial

@[hott] noncomputable theorem prop_uniq {α β : Type u} (p : α = β) :
  ua (idtoeqv p) = p :=
begin induction p, exact Jβrule end

@[hott] noncomputable theorem univalence (α β : Type u) :
  (α ≃ β) ≃ (α = β) := begin
  existsi ua, split; existsi idtoeqv,
  { intro e,
    refine J _ e,
    intro δ, transitivity,
    apply eq.map idtoeqv, apply Jβrule,
    reflexivity },
  { intro e, apply prop_uniq }
end

-- perfect proof
inductive so : bool → Type
| intro : so tt

namespace so
  def absurd {α : Type u} (x : so false) : α := by cases x
  theorem ff_neq_tt (h : ff = tt) : empty :=
  so.absurd (transport so h⁻¹ intro)
end so

@[hott] def is_zero : ℕ → bool
|      0       := tt
| (nat.succ _) := ff

@[hott] example (h : 0 = 1) : 𝟎 :=
ff_neq_tt (is_zero # h)⁻¹

@[hott] def succ_neq_zero {n : ℕ} : ¬(nat.succ n = 0) :=
λ h, ff_neq_tt (is_zero # h)

@[hott] def neg_bool_equiv : bool ≃ bool :=
begin existsi bnot, split; existsi bnot; intro x; induction x; trivial end

@[hott] noncomputable theorem universe_not_a_set : ¬(hset Type) :=
begin
  intro error,
  let p : bool = bool := ua neg_bool_equiv,
  let h := transport theorems.functions.idfun p tt,
  let g : h = ff := transport_rule neg_bool_equiv tt,
  let oops : h = tt :=
    (λ p, transport theorems.functions.idfun p tt) #
      (error p (idp bool)),
  let uh_oh : ff = tt := g⁻¹ ⬝ oops,
  apply ff_neq_tt, exact uh_oh
end

-- exercise 2.17 (i) in HoTT book
@[hott] noncomputable theorem product_equiv₁ {α α' β β' : Type u}
  (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') := begin
  have p := ua e₁, have q := ua e₂,
  induction p, induction q, reflexivity
end

@[hott] noncomputable theorem product_equiv₂ {α α' β β' : Type u}
  (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') :=
begin
  refine J _ e₁, intro A,
  refine J _ e₂, intro B,
  reflexivity
end

section
  open ground_zero.types.product
  @[hott] theorem product_equiv₃ {α α' β β' : Type u}
    (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') := begin
    cases e₁ with f H, induction H with linv rinv,
    cases linv with g α₁, induction rinv with h β₁,
  
    cases e₂ with f' H, induction H with linv' rinv',
    cases linv' with g' α₂, induction rinv' with h' β₂,
  
    existsi (bimap f f'), split,
    { existsi (bimap g g'), intro x,
      induction x with u v,
      apply construction,
      exact α₁ u, exact α₂ v },
    { existsi (bimap h h'), intro x,
      induction x with u v,
      apply construction,
      exact β₁ u, exact β₂ v }
  end
end

@[hott] theorem family_on_bool {π : bool → Type u} :
  (π ff × π tt) ≃ Π (b : bool), π b := begin
  let construct : (π ff × π tt) → Π (b : bool), π b := begin
    intros x b, cases x with p q,
    cases b, exact p, exact q
  end,
  let deconstruct : (Π (b : bool), π b) → (π ff × π tt) := begin
    intro H, split, exact H ff, exact H tt
  end,
  existsi construct, split; existsi deconstruct,
  { intro x, cases x with p q, reflexivity },
  { intro x, apply theorems.dfunext,
    intro b, induction b,
    repeat { reflexivity } }
end

end ua
end ground_zero