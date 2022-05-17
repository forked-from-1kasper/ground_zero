import ground_zero.support
open ground_zero.proto (idfun identity identity.elem identity.elim)
open combinator (S)

section
  universes u v
  variables {α : Type u} {β : Type v}

  abbreviation product := α × β
  def prod.Id {a c : α} {b d : β}
    (p : a = c :> α) (q : b = d :> β) : (a, b) = (c, d) :> α × β :=
  begin induction p, induction q, reflexivity end

  abbreviation prod.intro : α → β → α × β := prod.mk
  abbreviation prod.pr₁ : α × β → α := prod.fst
  abbreviation prod.pr₂ : α × β → β := prod.snd
end

namespace ground_zero.types
universes u v w k

hott theory

namespace equiv

  def homotopy {α : Type u} {π : α → Type v}
    (f g : Π (x : α), π x) :=
  Π (x : α), f x = g x :> π x
  infix ` ~ `:80 := homotopy

  @[hott, refl] def homotopy.id {α : Type u} {π : α → Type v}
    (f : Π (x : α), π x) : f ~ f :=
  begin intro x, reflexivity end

  @[hott] def homotopy.Id {α : Type u} {π : α → Type v}
    {f g : Π (x : α), π x} (h : f = g :> Π (x : α), π x) : f ~ g :=
  begin induction h, reflexivity end

  @[hott, symm] def homotopy.symm {α : Type u} {π : α → Type v}
    (f g : Π (x : α), π x) (h : f ~ g) : g ~ f :=
  λ x, (h x)⁻¹

  @[hott, trans] def homotopy.trans {α : Type u} {π : α → Type v}
    {f g h : Π (x : α), π x} (p : f ~ g) (q : g ~ h) : f ~ h :=
  λ x, p x ⬝ q x

  def linv {α : Type u} {β : Type v} (f : α → β) :=
  Σ (g : β → α), g ∘ f ~ id

  def rinv {α : Type u} {β : Type v} (f : α → β) :=
  Σ (g : β → α), f ∘ g ~ id

  def biinv {α : Type u} {β : Type v} (f : α → β) :=
  linv f × rinv f

  @[hott] def homotopy_square {α : Type u} {β : Type v}
    {f g : α → β} (H : f ~ g) {x y : α} (p : x = y :> α) :
    H x ⬝ (g # p) = (f # p) ⬝ H y :> f x = g y :> β :=
  begin
    induction p, transitivity,
    apply Id.refl_right,
    apply Id.refl_left
  end
end equiv

def equiv (α : Type u) (β : Type v) : Type (max u v) :=
Σ (f : α → β), equiv.biinv f
infix ` ≃ `:25 := equiv

namespace equiv
  instance forward_coe {α : Type u} {β : Type v} :
    has_coe (α ≃ β) (α → β) :=
  ⟨begin intro e, cases e with f H, exact f end⟩

  @[hott] def forward {α : Type u} {β : Type v} (e : α ≃ β) : α → β := e.fst

  @[hott] def left {α : Type u} {β : Type v} (e : α ≃ β) : β → α := e.2.1.1
  @[hott] def right {α : Type u} {β : Type v} (e : α ≃ β) : β → α := e.2.2.1

  @[hott] def left_forward {α : Type u} {β : Type v} (e : α ≃ β) : e.left ∘ e.forward ~ id := e.2.1.2
  @[hott] def forward_right {α : Type u} {β : Type v} (e : α ≃ β) : e.forward ∘ e.right ~ id := e.2.2.2

  @[hott, refl] def id (α : Type u) : α ≃ α :=
  begin existsi id, split; { existsi id, intro, reflexivity } end

  @[hott] def inveqv {α : Type u} {a b : α} : (a = b) ≃ (b = a) :=
  ⟨Id.inv, (⟨Id.inv, Id.inv_inv⟩, ⟨Id.inv, Id.inv_inv⟩)⟩

  @[hott] def biinv_trans {α : Type u} {β : Type v} {γ : Type w}
    {f : α → β} {g : β → γ} : biinv f → biinv g → biinv (g ∘ f)
  | (⟨g₁, G₁⟩, ⟨h₁, H₁⟩) (⟨g₂, G₂⟩, ⟨h₂, H₂⟩) :=
  begin
    split,
    { existsi (g₁ ∘ g₂), intro x, transitivity,
      apply Id.map g₁, apply G₂, exact G₁ x },
    { existsi (h₁ ∘ h₂), intro x, transitivity,
      apply Id.map g, apply H₁, exact H₂ x }
  end

  @[hott, trans] def trans {α : Type u} {β : Type v} {γ : Type w}
    (f : α ≃ β) (g : β ≃ γ) : α ≃ γ :=
  ⟨g.1 ∘ f.1, biinv_trans f.2 g.2⟩

  @[hott] def idtoeqv {α β : Type u} (p : α = β) : α ≃ β :=
  begin induction p, apply id end

  @[hott] def idtoiff {α β : Type u} (p : α = β) : α ↔ β :=
  begin induction p, reflexivity end

  @[hott] def transportconst {α β : Type u} : α = β → α → β :=
  forward ∘ idtoeqv

  def transportconst_inv {α β : Type u} : α = β → β → α :=
  left ∘ idtoeqv

  @[hott] def transportconst_over_inv {α β : Type u} (p : α = β) :
    Π x, transportconst p⁻¹ x = transportconst_inv p x :=
  begin intro x, induction p, trivial end

  @[hott] def subst {α : Type u} {π : α → Type v} {a b : α}
    (p : a = b :> α) : π a → π b :=
  begin induction p, exact idfun end

  @[hott] def happly {α : Type u} {β : Type v} {f g : α ≃ β}
    (p : f = g) : f.forward ~ g.forward :=
  begin induction p, reflexivity end

  -- subst with explicit π
  abbreviation transport {α : Type u}
    (π : α → Type v) {a b : α}
    (p : a = b :> α) : π a → π b :=
  subst p

  def dep_path {α : Type u} (π : α → Type v) {a b : α} (p : a = b :> α)
    (u : π a) (v : π b) :=
  equiv.subst p u = v :> π b

  notation u ` =[` P `,` p `] ` v := dep_path P p u v
  notation u ` =[` p `] ` v := dep_path _ p u v

  @[hott, refl] def dep_path.refl {α : Type u} (π : α → Type v) {a : α}
    (u : π a) : u =[Id.refl] u :=
  ground_zero.types.Id.refl

  @[hott] def pathover_of_eq {α : Type u} {β : Type v}
    {a b : α} {a' b' : β}
    (p : a = b :> α) (q : a' = b' :> β) : a' =[p] b' :=
  begin induction p, induction q, reflexivity end

  @[hott] def transport_forward_and_back {α : Type u} {β : α → Type v}
    {x y : α} (p : x = y :> α) (u : β x) :
    subst p⁻¹ (subst p u) = u :=
  begin induction p, trivial end

  @[hott] def transport_back_and_forward {α : Type u} {β : α → Type v}
    {x y : α} (p : x = y :> α) (u : β y) :
    subst p (subst p⁻¹ u) = u :=
  begin induction p, trivial end

  @[hott, symm] def dep_path.symm {α : Type u} {β : α → Type v} {a b : α}
    (p : a = b :> α) {u : β a} {v : β b}
    (q : u =[p] v) : v =[p⁻¹] u :=
  begin induction q, apply transport_forward_and_back end

  @[hott] def subst_comp {α : Type u}
    {π : α → Type v} {a b c : α}
    (p : a = b :> α) (q : b = c :> α) (x : π a) :
    subst (p ⬝ q) x = subst q (subst p x) :> π c :=
  begin induction p, induction q, trivial end

  @[hott, trans] def dep_trans {α : Type u} {π : α → Type v}
    {a b c : α} {p : a = b :> α} {q : b = c :> α}
    {u : π a} {v : π b} {w : π c}
    (r : u =[p] v) (s : v =[q] w):
    u =[p ⬝ q] w :=
  begin induction r, induction s, apply subst_comp end
  infix ` ⬝' `:40 := dep_trans

  @[hott] def subst_inv {α : Type u} {π : α → Type v} {a b : α}
    (p : a = b :> α) : π b → π a :=
  begin induction p, exact idfun end

  @[hott] def subst_over_path_comp {α : Type u} {π : α → Type v} {a b c : α}
    (p : a = b :> α) (q : b = c :> α) (x : π a) :
    subst (p ⬝ q) x = subst q (subst p x) :> π c :=
  begin induction p, reflexivity end

  @[hott] def subst_over_inv_path {α : Type u} {π : α → Type v} {a b : α}
    (p : a = b :> α) (x : π b) : subst p⁻¹ x = subst_inv p x :> π a :=
  begin induction p, reflexivity end

  reserve infix ` ▸ `
  infix [parsing_only] ` ▸ ` := subst

  @[hott] def apd {α : Type u} {β : α → Type v} {a b : α}
    (f : Π (x : α), β x) (p : a = b :> α) :
    subst p (f a) = f b :> β b :=
  begin induction p, reflexivity end

  @[hott] def apd_functoriality {α : Type u} {β : α → Type v} {a b c : α}
    (f : Π x, β x) (p : a = b :> α) (q : b = c :> α) :
    @apd α β a c f (p ⬝ q) = dep_trans (apd f p) (apd f q) :=
  begin induction p, induction q, reflexivity end

  @[hott] def subst_sqr {α : Type u} {π : α → Type v} {a b : α}
    {p q : a = b :> α} (r : p = q :> a = b :> α) (u : π a) :
    subst p u = subst q u :> π b :=
  begin induction r, reflexivity end
  notation `subst²` := subst_sqr

  @[hott] def dep_path_map {α : Type u} {π : α → Type v} {δ : α → Type w} {a b : α}
    {p : a = b :> α} {u : π a} {v : π b} (g : Π x, π x → δ x) (q : u =[p] v) : g a u =[p] g b v :=
  begin induction p, change u = v at q, induction q, reflexivity end

  @[hott] def dep_path_map' {α : Type u} {β : Type v} {π : α → Type w} {δ : β → Type k}
    {a b : α} {p : a = b :> α} {u : π a} {v : π b} (f : α → β)
      (g : Π x, π x → δ (f x)) (q : u =[p] v) : g a u =[f # p] g b v :=
  begin induction p, change u = v at q, induction q, reflexivity end

  abbreviation transport_inv {α : Type u}
    (π : α → Type v) {a b : α}
    (p : a = b :> α) : π b → π a :=
  subst_inv p

  abbreviation transport_sqr {α : Type u} (π : α → Type v) {a b : α}
    {p q : a = b :> α} (r : p = q :> a = b :> α) (u : π a) :
    subst p u = subst q u :> π b := subst_sqr r u
  notation `transport²` := transport_sqr

  @[hott] def transport_comp {α : Type u} {β : Type v}
    (π : β → Type w) {x y : α}
    (f : α → β) (p : x = y :> α) (u : π (f x)) :
    @subst α (π ∘ f) x y p u =
    subst (f # p) u :> π (f y) :=
  begin induction p, trivial end

  @[hott] def transport_to_transportconst {α : Type u} (π : α → Type v)
    {a b : α} (p : a = b) (u : π a) :
    equiv.transport π p u = equiv.transportconst (π # p) u :=
  begin induction p, trivial end

  @[hott] def transportconst_over_composition {α β γ : Type u}
    (p : α = β) (q : β = γ) (x : α) :
    transportconst (p ⬝ q) x = transportconst q (transportconst p x) :=
  begin induction p, induction q, trivial end

  @[hott] def transport_composition {α : Type u} {a x₁ x₂ : α}
    (p : x₁ = x₂ :> α) (q : a = x₁ :> α) :
    transport (Id a) p q = q ⬝ p :=
  begin
    induction p, symmetry, transitivity,
    apply Id.refl_right, trivial
  end

  @[hott] def transport_characterization
    {α : Type u} {β γ : α → Type v} {a b : α}
    (f : β a → γ a) (p : a = b) :
    subst p f = transport γ p ∘ f ∘ transport β p⁻¹ :=
  begin induction p, reflexivity end

  @[hott] def transport_over_family {α : Type u}
    {x y : α} {π δ : α → Type v}
    (f : Π (x : α), π x → δ x)
    (p : x = y :> α) (u : π x) :
    subst p (f x u) = f y (subst p u) :> δ y :=
  begin induction p, trivial end

  @[hott] def apd_sqr {α : Type u} {β γ : α → Type v} {a b : α}
    {u : β a} {v : β b} {p : a = b :> α}
    (f : Π {x : α} (u : β x), γ x) (q : u =[p] v) :
    f u =[p] f v :=
  begin induction p, induction q, reflexivity end

  @[hott] def apd₂ {α : Type u} {β : α → Type v} {a b : α}
    {p q : a = b :> α} (f : Π (x : α), β x)
    (r : p = q :> a = b :> α) :
    apd f p =[r] apd f q :=
  begin induction r, reflexivity end

  @[hott] def rewrite_comp {α : Type u} {a b c : α}
    {p : a = b} {q : b = c} {r : a = c}
    (h : r = p ⬝ q) : p⁻¹ ⬝ r = q :=
  begin induction p, exact Id.refl_left r ⬝ h end

  @[hott] def inv_rewrite_comp {α : Type u} {a b c : α}
    {p : a = b} {q : b = c} {r : a = c}
    (h : p⁻¹ ⬝ r = q) : r = p ⬝ q :=
  begin induction p, exact Id.refl_left r ⬝ h end

  @[hott] def inv_comp_rewrite {α : Type u} {a b c : α}
    {p : a = b} {q : b = c} {r : a = c}
    (h : p ⬝ q = r) : p = r ⬝ q⁻¹ :=
  begin induction q, exact (Id.refl_right p)⁻¹ ⬝ h ⬝ (Id.refl_right r)⁻¹ end

  @[hott] def pathover_from_trans {α : Type u} {a b c : α}
    (p : b = c :> α) (q : a = b :> α) (r : a = c :> α) :
    (q ⬝ p = r :> a = c :> α) → (q =[p] r) :=
  begin intro h, induction h, apply transport_composition end

  @[hott] def transport_inv_comp_comp {α : Type u} {a b : α} (p : a = b) (q : a = a) :
    equiv.transport (λ x, x = x) p q = p⁻¹ ⬝ q ⬝ p :=
  begin
    induction p, symmetry, transitivity,
    apply Id.refl_left (q ⬝ Id.refl), transitivity,
    apply Id.refl_right, trivial
  end

  @[hott] def map_functoriality {α : Type u} {β : Type v}
    {a b c : α} (f : α → β) {p : a = b} {q : b = c} :
    f # (p ⬝ q) = (f # p) ⬝ (f # q) :=
  begin induction p, trivial end

  @[hott] def transport_over_contr_map {α : Type u} {β : Type v} {a b : α} {c : β}
    (f : α → β) (p : a = b) (q : f a = c) :
    equiv.transport (λ x, f x = c) p q = f # p⁻¹ ⬝ q :=
  begin induction p, trivial end

  @[hott] def transport_over_inv_contr_map {α : Type u} {β : Type v} {a b : α} {c : β}
    (f : α → β) (p : a = b) (q : c = f a) :
    equiv.transport (λ x, c = f x) p q = q ⬝ f # p :=
  begin induction p, symmetry, apply Id.refl_right end

  @[hott] def transport_over_involution {α : Type u} {a b : α}
    (f : α → α) (p : a = b) (q : f a = a) :
    equiv.transport (λ x, f x = x) p q = (f # p⁻¹) ⬝ q ⬝ p :=
  begin
    induction p, symmetry,
    transitivity, apply Id.refl_left (q ⬝ Id.refl),
    apply Id.refl_right
  end

  @[hott] def transport_over_hmtpy {α : Type u} {β : Type v} {a b : α}
    (f g : α → β) (p : a = b) (q : f a = g a) :
    equiv.transport (λ x, f x = g x) p q = (f # p⁻¹) ⬝ q ⬝ g # p :=
  begin
    induction p, symmetry,
    transitivity, apply Id.refl_left,
    apply Id.refl_right
  end

  @[hott] def idmap {α : Type u} {a b : α} (p : a = b) : idfun # p = p :=
  begin induction p, trivial end

  @[hott] def constmap {α : Type u} {β : Type v} {a b : α} {c : β}
    (p : a = b) : (λ _, c) # p = Id.refl :=
  begin induction p, trivial end

  @[hott] def transport_over_dhmtpy {α : Type u} {β : α → Type v} {a b : α}
    (f g : Π x, β x) (p : a = b) (q : f a = g a) :
    equiv.transport (λ x, f x = g x) p q = (apd f p)⁻¹ ⬝ subst p # q ⬝ apd g p :=
  begin
    induction p, symmetry,
    transitivity, apply Id.map (⬝ apd g _), apply Id.refl_left,
    transitivity, apply Id.map, apply idmap,
    transitivity, apply Id.refl_right,
    trivial
  end

  @[hott] def map_over_comp {α : Type u} {β : Type v} {γ : Type w} {a b : α}
    (f : α → β) (g : β → γ) (p : a = b) :
    @Id.map α γ a b (g ∘ f) p = g # (f # p) :> g (f a) = g (f b) :> γ :=
  begin induction p, trivial end

  @[hott] def apd_over_constant_family {α : Type u} {β : Type v} {a b : α}
    (f : α → β) (p : a = b :> α) :
    apd f p = pathover_of_eq p (f # p) :=
  begin induction p, trivial end

  def refl_pathover {α : Type u} {β : Type v} {a : α} {x y : β}
    (p : x =[idp a] y) : x = y := p

  @[hott] def pathover_inv {α : Type u} {β : Type v} (a : α) {x y : β} (p : x = y) :
    refl_pathover (pathover_of_eq (idp a) p) = p :=
  begin induction p, reflexivity end

  @[hott] def pathover_of_eq_inj {α : Type u} {β : Type v} {a b : α} {a' b' : β}
    (r : a = b :> α) (p q : a' = b' :> β) :
    pathover_of_eq r p = pathover_of_eq r q → p = q :=
  begin
    intro H, induction r, induction p,
    transitivity, symmetry, apply pathover_inv a,
    symmetry, transitivity, symmetry, apply pathover_inv a,
    symmetry, exact refl_pathover # H
  end

  @[hott] def transport_impl {α : Type u} (μ : α → Type v)
    (η : α → Type w) {a b : α} (p : a = b) (φ : μ a → η a) :
    transport (λ x, μ x → η x) p φ = λ x, subst p (φ (subst p⁻¹ x)) :=
  begin induction p, reflexivity end

  @[hott] def transport_over_const_family {α : Type u} {β : Type v}
    {a b : α} (p : a = b) (b : β) : transport (λ _, β) p b = b :=
  begin induction p, reflexivity end

  @[hott] def transport_over_pi {α : Type u} {a b : α} {β : Type v}
    (π : α → β → Type w) (p : a = b) (u : Π (y : β), π a y) :
    transport (λ x, Π y, π x y) p u =
    (λ y, @transport α (λ x, π x y) a b p (u y)) :=
  begin induction p, trivial end

  @[hott] def transport_over_function {α : Type u} {β : Type v}
    {a : α} {b : β} (f g : α → β) (p : f = g) (q : f a = b) :
    transport (λ (f' : α → β), f' a = b) p q =
    @Id.map (α → β) β g f (λ (f' : α → β), f' a) p⁻¹ ⬝ q :=
  begin induction p, trivial end

  @[hott] def transport_over_operation {α β : Type u} (φ : α → α → α) (p : α = β) :
    transport (λ α, α → α → α) p φ = λ x y, subst p (φ (subst p⁻¹ x) (subst p⁻¹ y)) :=
  begin induction p, reflexivity end

  @[hott] def transport_over_functor {α β : Type u}
    (μ : Type u → Type v) (η : Type u → Type w) (φ : μ α → η α) (p : α = β) :
    transport (λ α, μ α → η α) p φ = λ x, subst p (φ (subst p⁻¹ x)) :=
  begin induction p, reflexivity end

  @[hott] def transport_over_morphism {α β : Type u} (φ : α → α) (p : α = β) :
    transport (λ α, α → α) p φ = λ x, subst p (φ (subst p⁻¹ x)) :=
  begin induction p, reflexivity end

  @[hott] def transport_over_operation_pointwise {α β : Type u} (φ : α → α → α) (p : α = β)
    {x y : β} : transport (λ α, α → α → α) p φ x y = subst p (φ (subst p⁻¹ x) (subst p⁻¹ y)) :=
  begin induction p, reflexivity end

  @[hott] def transport_over_morphism_pointwise {α β : Type u} (φ : α → α) (p : α = β)
    {x : β} : transport (λ α, α → α) p φ x = subst p (φ (subst p⁻¹ x)) :=
  begin induction p, reflexivity end

  @[hott] def bimap {α : Type u} {β : Type v} {γ : Type w}
    {a b : α} {a' b' : β} (f : α → β → γ)
    (p : a = b) (q : a' = b') : f a a' = f b b' :=
  begin induction p, induction q, reflexivity end

  @[hott] def bimap_refl_left {α : Type u} {β : Type v} {γ : Type w}
    {a : α} {a' b' : β} (f : α → β → γ) (p : a' = b') :
    bimap f (idp a) p = f a # p :=
  begin induction p, trivial end

  @[hott] def bimap_refl_right {α : Type u} {β : Type v} {γ : Type w}
    {a b : α} {a' : β} (f : α → β → γ) (p : a = b) :
    bimap f p (idp a') = (λ x, f x a') # p :=
  begin induction p, trivial end

  @[hott] def bimap_characterization {α : Type u} {β : Type v} {γ : Type w}
    {a b : α} {a' b' : β} (f : α → β → γ)
    (p : a = b) (q : a' = b') :
    bimap f p q = @Id.map α γ a b (λ x, f x a') p ⬝ f b # q :=
  begin induction p, trivial end

  @[hott] def bimap_characterization' {α : Type u} {β : Type v} {γ : Type w}
    {a b : α} {a' b' : β} (f : α → β → γ)
    (p : a = b) (q : a' = b') :
    bimap f p q = f a # q ⬝ @Id.map α γ a b (λ x, f x b') p :=
  begin induction p, induction q, trivial end

  @[hott] def bimap_inv {α : Type u} {β : Type v} {γ : Type w}
    {a b : α} {a' b' : β} (f : α → β → γ)
    (p : a = b) (q : a' = b') : (bimap f p q)⁻¹ = bimap f p⁻¹ q⁻¹ :=
  begin induction p, induction q, trivial end

  @[hott] def bimap_comp {α : Type u} {β : Type v} {γ : Type w}
    {a b : α} {a' b' : β} (f : α → β → γ) (p : a = b) (q : a' = b') :
    (λ x, f x a') # p = f a # q ⬝ bimap f p q⁻¹ :=
  begin
    induction p, symmetry,
    transitivity, { apply Id.map, apply bimap_refl_left },
    transitivity, { apply Id.map, apply Id.map_inv },
    apply Id.comp_inv
  end

  @[hott] def map_over_S {α : Type u} {a b : α}
    (f : α → α → α) (g : α → α) (p : a = b) :
    (S f g # p) = @bimap α α α a b (g a) (g b) f p (g # p) :=
  begin induction p, reflexivity end

  @[hott] def lifted_happly {α : Type u} (μ : α → Type v) (η : α → Type w)
    {a b : α} (p : a = b) (f : μ a → η a) (g : μ b → η b)
    (q : transport (λ x, μ x → η x) p f = g) :
    Π (x : μ a), transport η p (f x) = g (transport μ p x) :=
  begin induction p, induction q, intro x, trivial end

  @[hott] def identity_eqv {α : Type u} : α ≃ identity α :=
  begin
    existsi identity.elem, split; existsi identity.elim; intro x,
    { reflexivity }, { induction x, reflexivity }
  end

  @[hott, trans] def eqv_eq_eqv {α β γ : Type u}
    (p : α ≃ β) (q : β = γ) : α ≃ γ :=
  transport (equiv α) q p
end equiv

def is_qinv {α : Type u} {β : Type v} (f : α → β) (g : β → α) :=
(f ∘ g ~ id) × (g ∘ f ~ id)

class has_qinv {α : Type u} {β : Type v} (f : α → β) :=
(inv : β → α) (lawful : is_qinv f inv)
postfix ⁻¹ := has_qinv.inv

def qinv {α : Type u} {β : Type v} (f : α → β) :=
Σ (g : β → α), is_qinv f g

namespace qinv
  def eqv (α : Type u) (β : Type v) :=
  Σ (f : α → β), qinv f

  @[hott] def to_biinv {α : Type u} {β : Type v} (f : α → β) (q : qinv f) : equiv.biinv f :=
  (⟨q.1, q.2.2⟩, ⟨q.1, q.2.1⟩)

  @[hott] def linv_inv {α : Type u} {β : Type v}
    (f : α → β) (g : β → α) (h : β → α)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : g ∘ f ~ id :=
  let F₁ := λ x, H (g (f x)) in
  let F₂ := λ x, h # (G (f x)) in
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ H x

  @[hott] def rinv_inv {α : Type u} {β : Type v}
    (f : α → β) (g : β → α) (h : β → α)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : f ∘ h ~ id :=
  let F₁ := λ x, (f ∘ h) # (G x) in
  let F₂ := λ x, f # (H (g x)) in
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ G x

  @[hott] def of_biinv {α : Type u} {β : Type v} (f : α → β) (F : equiv.biinv f) : qinv f :=
  ⟨F.2.1, (F.2.2, linv_inv f F.2.1 F.1.1 F.2.2 F.1.2)⟩

  @[hott] def inv {α : Type u} {β : Type v} (e : eqv α β) : eqv β α :=
  ⟨e.2.1, ⟨e.1, (e.2.2.2, e.2.2.1)⟩⟩

  @[hott] def to_equiv {α : Type u} {β : Type v} (e : eqv α β) : α ≃ β :=
  ⟨e.1, (⟨e.2.1, e.2.2.2⟩, ⟨e.2.1, e.2.2.1⟩)⟩
end qinv

@[hott] def equiv.forward_left {α : Type u} {β : Type v}
  (e : α ≃ β) : e.forward ∘ e.left ~ id :=
begin apply qinv.rinv_inv, apply e.forward_right, apply e.left_forward end

@[hott] def equiv.right_forward {α : Type u} {β : Type v}
  (e : α ≃ β) : e.right ∘ e.forward ~ id :=
begin apply qinv.linv_inv, apply e.forward_right, apply e.left_forward end

namespace equiv
  @[hott, symm] def symm {α : Type u} {β : Type v} (f : α ≃ β) : β ≃ α :=
  qinv.to_equiv (qinv.inv ⟨f.1, qinv.of_biinv f.1 f.2⟩)
end equiv

-- half adjoint equivalence
def ishae {α : Type u} {β : Type v} (f : α → β) :=
Σ (g : β → α) (η : g ∘ f ~ id) (ϵ : f ∘ g ~ id),
  Π x, f # (η x) = ϵ (f x) :> f (g (f x)) = f x :> β

def fib {α : Type u} {β : Type v} (f : α → β) (y : β) :=
Σ (x : α), f x = y :> β

def total {α : Type u} (β : α → Type v) := Σ x, β x
def fiberwise {α : Type u} (β : α → Type v) := Π x, β x

end ground_zero.types