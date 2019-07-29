import ground_zero.types.product
open ground_zero.types.equiv (idtoeqv homotopy)
open ground_zero.types.equiv (renaming id -> ideqv)
open ground_zero.types.eq (renaming refl -> idp)
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

local infix ` = ` := types.eq
universes u v

axiom J {π : Π (α β : Sort u), α ≃ β → Sort v}
  (h : Π (α : Sort u), π α α (ideqv α))
  {α β : Sort u} (e : α ≃ β) : π α β e
axiom Jβrule {π : Π (α β : Sort u), α ≃ β → Sort v}
  {h : Π (α : Sort u), π α α (ideqv α)} {α : Sort u} :
  J h (ideqv α) = h α :> π α α (ideqv α)

noncomputable abbreviation Jrule
  (π : Π (α β : Sort u), α ≃ β → Sort v)
  (h : Π (α : Sort u), π α α (ideqv α))
  {α β : Sort u} (e : α ≃ β) : π α β e :=
J h e

noncomputable def ua {α β : Sort u} : α ≃ β → α = β :=
J idp

namespace ua

noncomputable theorem refl_on_ua (α : Sort u) :
  ua (ideqv α) = idp α :=
begin unfold ua, exact Jβrule end

noncomputable theorem comp_rule {α β : Sort u} (e : α ≃ β) :
  Π (x : α), x =[ua e] e.fst x := begin
  refine J _ e, intros ψ x,
  refine types.eq.rec _ (refl_on_ua ψ)⁻¹,
  reflexivity
end

noncomputable theorem transport_rule {α β : Sort u} (e : α ≃ β) :
  Π (x : α), types.equiv.subst (ua e) x = e.fst x := begin
  refine J _ e, intros ψ x,
  refine types.eq.rec _ (refl_on_ua ψ)⁻¹,
  reflexivity
end

noncomputable theorem transport_inv_rule {α β : Sort u} (e : α ≃ β) :
  Π (x : β), types.equiv.subst_inv (ua e) x = e.backward x := begin
  refine J _ e, intros ψ x,
  refine types.eq.rec _ (refl_on_ua ψ)⁻¹,
  reflexivity
end

theorem idtoeqv_and_id {α : Sort u} :
  idtoeqv (idp α) = ideqv α :=
begin simp [idtoeqv] end

noncomputable theorem prop_uniq {α β : Sort u} (p : α = β) :
  ua (idtoeqv p) = p := begin
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

-- perfect proof
inductive so : bool → Type
| intro : so tt

namespace so
  def absurd {α : Sort u} (x : so false) : α := by cases x
  theorem ff_neq_tt (h : ff = tt) : empty :=
  so.absurd (transport so h⁻¹ intro)
end so

def is_zero : ℕ → bool
| 0 := tt
| _ := ff

example (h : 0 = 1) : 𝟎 :=
ff_neq_tt (is_zero # h)⁻¹

def succ_neq_zero {n : ℕ} : ¬(nat.succ n = 0) :=
λ h, ff_neq_tt (is_zero # h)

def neg_bool_equiv : bool ≃ bool := begin
  existsi bnot, split; existsi bnot; intro x; simp
end

noncomputable theorem universe_not_a_set : ¬(hset Type) :=
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
noncomputable theorem product_equiv₁ {α α' β β' : Sort u}
  (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') := begin
  have p := ua e₁, have q := ua e₂,
  induction p, induction q, reflexivity
end

noncomputable theorem product_equiv₂ {α α' β β' : Sort u}
  (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') :=
begin
  refine J _ e₁, intro A,
  refine J _ e₂, intro B,
  reflexivity
end

section
  open ground_zero.types.product
  theorem product_equiv₃ {α α' β β' : Sort u}
    (e₁ : α ≃ α') (e₂ : β ≃ β') : (α × β) ≃ (α' × β') := begin
    cases e₁ with f H, cases H with linv rinv,
    cases linv with g α₁, cases rinv with h β₁,
  
    cases e₂ with f' H, cases H with linv' rinv',
    cases linv' with g' α₂, cases rinv' with h' β₂,
  
    existsi (bimap f f'), split,
    { existsi (bimap g g'), intro x,
      cases x with u v, simp [*],
      apply construction,
      exact α₁ u, exact α₂ v },
    { existsi (bimap h h'), intro x,
      cases x with u v, simp [*],
      apply construction,
      exact β₁ u, exact β₂ v }
  end
end

theorem family_on_bool {π : bool → Sort u} :
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
  { intro x, apply HITs.interval.dfunext,
    intro b, induction b,
    repeat { reflexivity } }
end

end ua
end ground_zero