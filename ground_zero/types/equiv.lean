import ground_zero.support ground_zero.theorems.functions ground_zero.types.dep_path

namespace ground_zero.types

hott theory

structure {u v} product (α : Sort u) (β : Sort v) :=
intro :: (pr₁ : α) (pr₂ : β)
attribute [pp_using_anonymous_constructor] product

reserve infix ` × `
infix ` × ` := product

def {u v} product.eq {α : Sort u} {β : Sort v} {a c : α} {b d : β}
  (p : a = c) (q : b = d) : ⟨a, b⟩ = ⟨c, d⟩ :> α × β :=
begin induction p, induction q, reflexivity end

namespace equiv
  universes u v

  def homotopy {α : Sort u} {π : α → Sort v}
    (f g : Π (x : α), π x) :=
  Π (x : α), f x = g x :> π x
  infix ` ~ ` := homotopy

  @[refl] def homotopy.id {α : Sort u} {π : α → Sort v}
    (f : Π (x : α), π x) : f ~ f :=
  begin simp [homotopy], intro x, reflexivity end

  def homotopy.eq {α : Sort u} {π : α → Sort v}
    {f g : Π (x : α), π x} (h : f = g :> Π (x : α), π x) : f ~ g :=
  begin induction h, reflexivity end

  @[symm] def homotopy.symm {α : Sort u} {π : α → Sort v}
    (f g : Π (x : α), π x) (h : f ~ g) : g ~ f := begin
    simp [homotopy] at *, intros,
    apply eq.symm, apply h
  end

  @[trans] def homotopy.trans {α : Sort u} {π : α → Sort v}
    (f g h : Π (x : α), π x) (r₁ : f ~ g) (r₂ : g ~ h) : f ~ h := begin
    simp [homotopy] at *, intros, transitivity,
    apply r₁, apply r₂
  end

  def linv {α : Sort u} {β : Sort v} (f : α → β) :=
  Σ' (g : β → α), g ∘ f ~ id

  def rinv {α : Sort u} {β : Sort v} (f : α → β) :=
  Σ' (g : β → α), f ∘ g ~ id

  def biinv {α : Sort u} {β : Sort v} (f : α → β) :=
  linv f × rinv f

  def homotopy_sqaure {α : Sort u} {β : Sort v}
    {f g : α → β} (H : f ~ g) {x y : α}
    (p : x = y :> α) :
    H x ⬝ (g # p) = (f # p) ⬝ H y :> f x = g y :> β := begin
    induction p, transitivity,
    apply eq.refl_right,
    apply eq.refl_left
  end
end equiv

def {u v} equiv (α : Sort u) (β : Sort v) :=
Σ' (f : α → β), equiv.biinv f
infix ` ≃ `:25 := equiv

namespace equiv
  universes u v w

  instance forward_coe {α : Sort u} {β : Sort v} :
    has_coe (α ≃ β) (α → β) :=
  ⟨begin intro e, cases e with f H, exact f end⟩

  def forward {α : Sort u} {β : Sort v} (e : α ≃ β) : α → β := e.fst
  def backward {α : Sort u} {β : Sort v} (e : α ≃ β) : β → α := begin
    cases e with f e, cases e with linv rinv,
    cases linv with g G, exact g
  end

  @[refl] def id (α : Sort u) : α ≃ α := begin
    existsi id, split,
    repeat {
      existsi id, intro, reflexivity
    }
  end

  @[trans] def trans {α : Sort u} {β : Sort v} {γ : Sort w}
    (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ := begin
    cases e₁ with f₁ H₁,
    cases H₁ with linv₁ rinv₁,
    cases linv₁ with g₁ α₁,
    cases rinv₁ with h₁ β₁,

    cases e₂ with f₂ H₂,
    cases H₂ with linv₂ rinv₂,
    cases linv₂ with g₂ α₂,
    cases rinv₂ with h₂ β₂,

    existsi (f₂ ∘ f₁), split,
    { existsi (g₁ ∘ g₂),
      intro x, simp, transitivity,
      exact g₁ # (α₂ (f₁ x)), exact α₁ x },
    { existsi (h₁ ∘ h₂),
      intro x, simp, transitivity,
      exact f₂ # (β₁ (h₂ x)), exact β₂ x }
  end

  def idtoeqv {α β : Sort u} (p : α = β :> _) : α ≃ β :=
  begin induction p, apply id end

  def transportconst {α β : Sort u} : (α = β :> _) → (α → β) :=
  psigma.fst ∘ idtoeqv

  def subst {α : Sort u} {π : α → Sort v} {a b : α}
    (p : a = b :> α) : π a → π b :=
  begin induction p, exact ground_zero.theorems.functions.idfun end

  def subst_inv {α : Sort u} {π : α → Sort v} {a b : α}
    (p : a = b :> α) : π b → π a :=
  begin induction p, exact ground_zero.theorems.functions.idfun end

  theorem subst_over_path_comp {α : Sort u} {π : α → Sort v} {a b c : α}
    (p : a = b :> α) (q : b = c :> α) (x : π a) :
    subst (p ⬝ q) x = subst q (subst p x) :> π c :=
  begin induction p, reflexivity end

  theorem subst_over_inv_path {α : Sort u} {π : α → Sort v} {a b : α}
    (p : a = b :> α) (x : π b) : subst p⁻¹ x = subst_inv p x :> π a :=
  begin induction p, reflexivity end

  reserve infix ` ▸ `
  infix [parsing_only] ` ▸ ` := subst

  def apd {α : Sort u} {β : α → Sort v} {a b : α}
    (f : Π (x : α), β x) (p : a = b :> α) :
    subst p (f a) = f b :> β b :=
  begin induction p, reflexivity end

  def subst_sqr {α : Sort u} {π : α → Sort v} {a b : α}
    {p q : a = b :> α} (r : p = q :> a = b :> α) (u : π a) :
    subst p u = subst q u :> π b :=
  begin induction r, reflexivity end
  notation `subst²` := subst_sqr

  lemma dep_path_map {α : Sort u}
    {π : α → Sort v} {δ : α → Sort w}
    {a b : α}
    {p : a = b :> α} {u : π a} {v : π b} (q : u =[p] v)
    (g : Π {x : α}, π x → δ x) :
    g u =[p] g v :=
  begin induction q, induction p, trivial end

  def subst_comp {α : Sort u}
    {π : α → Sort v} {a b c : α}
    (p : a = b :> α) (q : b = c :> α) (x : π a) :
    subst (p ⬝ q) x = subst q (subst p x) :> π c :=
  begin induction p, induction q, trivial end

  -- subst with explicit π
  abbreviation transport {α : Sort u}
    (π : α → Sort v) {a b : α}
    (p : a = b :> α) : π a → π b := subst p
  
  abbreviation transport_inv {α : Sort u}
    (π : α → Sort v) {a b : α}
    (p : a = b :> α) : π b → π a := subst_inv p

  abbreviation transport_sqr {α : Sort u} (π : α → Sort v) {a b : α}
    {p q : a = b :> α} (r : p = q :> a = b :> α) (u : π a) :
    subst p u = subst q u :> π b := subst_sqr r u
  notation `transport²` := transport_sqr

  --notation u ` =[` P `,` p `] ` v := transport P p u = v :> _

  def transport_comp {α : Sort u} {β : Sort v}
    (π : β → Sort w) {x y : α}
    (f : α → β) (p : x = y :> α) (u : π (f x)) :
    @subst _ (π ∘ f) _ _ p u =
    subst (f # p) u :> π (f y) :=
  begin induction p, trivial end

  def transport_composition {α : Sort u} {a x₁ x₂ : α}
    (p : x₁ = x₂ :> α) (q : a = x₁ :> α) :
    transport (ground_zero.types.eq a) p q = q ⬝ p :> _ := begin
    induction p, symmetry, transitivity,
    apply eq.refl_right, trivial
  end

  def transport_characterization
    {α : Sort u} {β γ : α → Sort v} {a b : α}
    (f : β a → γ a) (p : a = b) :
    subst p f = transport γ p ∘ f ∘ transport β p⁻¹ :=
  begin induction p, reflexivity end

  lemma transport_over_family {α : Sort u}
    {x y : α} {π δ : α → Sort v}
    (f : Π (x : α), π x → δ x)
    (p : x = y :> α) (u : π x) :
    subst p (f x u) = f y (subst p u) :> δ y :=
  begin induction p, trivial end

  def apd_sqr {α : Sort u} {β γ : α → Sort v} {a b : α}
    {u : β a} {v : β b} {p : a = b :> α}
    (f : Π {x : α} (u : β x), γ x) (q : u =[p] v) :
    f u =[p] f v :=
  begin induction q, reflexivity end

  def apd₂ {α : Sort u} {β : α → Sort v} {a b : α}
    {p q : a = b :> α} (f : Π (x : α), β x)
    (r : p = q :> a = b :> α) :
    dep_path.apd f p =[r] dep_path.apd f q :=
  begin induction r, reflexivity end

  def rewrite_comp {α : Sort u} {a b c : α}
    {p : a = b :> α} {q : b = c :> α} {r : a = c :> α}
    (h : r = p ⬝ q :> a = c :> α) :
    p⁻¹ ⬝ r = q :> b = c :> α := begin
    induction p, unfold eq.symm, transitivity,
    exact eq.refl_left r, exact h ⬝ eq.refl_left q
  end

  def path_over_subst {α : Sort u} {β : α → Sort v}
    {a b : α} {p : a = b :> α} {u : β a} {v : β b}
    (q : subst p u = v :> β b) : u =[p] v :=
  begin induction q, induction p, reflexivity end

  def subst_from_pathover {α : Sort u} {β : α → Sort v}
    {a b : α} {p : a = b :> α} {u : β a} {v : β b}
    (q : u =[p] v) : subst p u = v :> β b :=
  begin induction q, reflexivity end

  def pathover_from_trans {α : Sort u} {a b c : α}
    (p : b = c :> α) (q : a = b :> α) (r : a = c :> α) :
    (q ⬝ p = r :> a = c :> α) → (q =[p] r) := begin
    intro h, induction h,
    apply path_over_subst, apply transport_composition
  end

  def transport_forward_and_back {α : Sort u} {β : α → Sort v}
    {x y : α} (p : x = y :> α) (u : β x) :
    subst p⁻¹ (subst p u) = u :=
  begin induction p, trivial end

  def transport_back_and_forward {α : Sort u} {β : α → Sort v}
    {x y : α} (p : x = y :> α) (u : β y) :
    subst p (subst p⁻¹ u) = u :=
  begin induction p, trivial end
end equiv

def {u v} is_qinv {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) :=
(f ∘ g ~ id) × (g ∘ f ~ id)

class {u v} has_qinv {α : Sort u} {β : Sort v} (f : α → β) :=
(inv : β → α) (lawful : is_qinv f inv)
postfix ⁻¹ := has_qinv.inv

def {u v} qinv {α : Sort u} {β : Sort v} (f : α → β) :=
Σ' (g : β → α), is_qinv f g

namespace qinv
  universes u v w

  def equiv (α : Sort u) (β : Sort v) :=
  Σ' (f : α → β), qinv f

  def q2b {α : Sort u} {β : Sort v} (f : α → β) (q : qinv f) :
    equiv.biinv f := begin
    cases q with g H,
    cases H with α β,
    split; existsi g,
    exact β, exact α
  end

  def linv_inv {α : Sort u} {β : Sort v}
    (f : α → β) (g : β → α) (h : β → α)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : g ∘ f ~ id :=
  let F₁ := λ x, H (g (f x)) in
  let F₂ := λ x, h # (G (f x)) in
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ H x

  def rinv_inv {α : Sort u} {β : Sort v}
    (f : α → β) (g : β → α) (h : β → α)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : f ∘ h ~ id :=
  let F₁ := λ x, (f ∘ h) # (G x) in
  let F₂ := λ x, f # (H (g x)) in
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ G x

  def b2q {α : Sort u} {β : Sort v} (f : α → β)
    (b : equiv.biinv f) : qinv f := begin
    cases b with linv rinv,
    cases rinv with g α,
    cases linv with h β,

    existsi g, split, exact α, apply linv_inv; assumption
  end
end qinv

namespace equiv
  universes u v

  @[symm] def symm {α : Sort u} {β : Sort v}
    (e : α ≃ β) : β ≃ α := begin
    cases e with f H, have q := qinv.b2q f H,
    cases q with g qinv, cases qinv with α β,
    existsi g, split; existsi f,
    exact α, exact β
  end
end equiv

-- half adjoint equivalence
def {u v} ishae {α : Sort u} {β : Sort v} (f : α → β) :=
Σ' (g : β → α) (η : g ∘ f ~ id) (ϵ : f ∘ g ~ id) (x : α),
  f # (η x) = ϵ (f x) :> f (g (f x)) = f x :> β

def {u v} fib {α : Sort u} {β : Sort v} (f : α → β) (y : β) :=
Σ' (x : α), f x = y :> β

end ground_zero.types