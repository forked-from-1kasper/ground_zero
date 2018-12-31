import ground_zero.cubical.cubes
open ground_zero.cubical.cubes ground_zero.types ground_zero.HITs
open ground_zero.HITs.interval (i₀ i₁ seg)

namespace ground_zero.cubical.path
universes u v

def coe (π : I → Sort u) (x : π i₀) : Π i, π i :=
interval.ind x (equiv.subst seg x) (equiv.path_over_subst eq.rfl)

@[refl] def refl {α : Sort u} (a : α) : a ⇝ a := <i> a
@[refl] def rfl {α : Sort u} {a : α} : a ⇝ a := <i> a

@[symm] def symm {α : Sort u} {a b : α} (p : a ⇝ b) : b ⇝ a :=
<i> p # −i
postfix `⁻¹` := symm

abbreviation inv {α : Sort u} {a b : α} (p : a ⇝ b) := p⁻¹

def funext {α : Sort u} {β : α → Sort v} {f g : Π (x : α), β x}
  (p : Π (x : α), f x ⇝ g x) : f ⇝ g :=
<i> λ x, (p x) # i

def cong {α : Sort u} {β : Sort v} {a b : α}
  (f : α → β) (p : a ⇝ b) : f a ⇝ f b :=
<i> f (p # i)

def ap {α : Sort u} {β : α → Sort v} {a b : α}
  (f : α → β a) (p : a ⇝ b) : f a ⇝ f b :=
<i> f (p # i)

def subst {α : Sort u} {π : α → Sort v} {a b : α}
  (p : a ⇝ b) (x : π a) : π b :=
coe (λ i, π (p # i)) x i₁

abbreviation transport {α : Sort u} (π : α → Sort v) {a b : α}
  (p : a ⇝ b) : π a → π b := subst p

def trans {α β : Sort u} : (α ⇝ β) → (α → β) :=
transport id
abbreviation coerce {α β : Sort u} : (α ⇝ β) → (α → β) := trans

def idtoeqv {α β : Sort u} (p : α ⇝ β) : α ≃ β :=
trans (<i> α ≃ p # i) (equiv.id α)

def test_eta {α : Sort u} {a b : α} (p : a ⇝ b) : p ⇝ p := rfl
def face₀ {α : Sort u} {a b : α} (p : a ⇝ b) : α := p # 0
def face₁ {α : Sort u} {a b : α} (p : a ⇝ b) : α := p # 1

def comp_test₀ {α : Sort u} {a b : α} (p : a ⇝ b) : p # 0 ⇝ a := rfl
def comp_test₁ {α : Sort u} {a b : α} (p : a ⇝ b) : p # 1 ⇝ b := rfl

-- fail
--def symm_test {α : Type u} {a b : α} (p : a ⇝ b) : (p⁻¹)⁻¹ ⇝ p := rfl
@[trans] def composition {α : Sort u} {a b c : α}
  (p : a ⇝ b) (q : b ⇝ c) : a ⇝ c := subst q p

infix ⬝ := composition

-- this will be replaced by a more general version in future
def kan {α : Sort u} {a b c d : α}
  (bottom : b ⇝ c) (left : b ⇝ a) (right : c ⇝ d) : a ⇝ d :=
left⁻¹ ⬝ bottom ⬝ right

def kan_op {α : Sort u} {a b : α} (p : a ⇝ a) (q : a ⇝ b) : b ⇝ b :=
kan p q q

def interval_contr (i : I) : i₀ ⇝ i := coe (λ i, i₀ ⇝ i) rfl i
def seg_path : i₀ ⇝ i₁ := interval_contr i₁

-- or too direct way
example : i₀ ⇝ i₁ := <i> i

def conn_and {α : Sort u} {a b : α} (p : a ⇝ b) :
  LineP (λ i, a ⇝ p # i) :=
λ i, <j> p # i ∧ j

def conn_or {α : Sort u} {a b : α} (p : a ⇝ b) :
  LineP (λ i, p # i ⇝ b) :=
λ i, <j> p # i ∨ j

def singl {α : Sort u} (a : α) :=
Σ' (x : α), a ⇝ x

def eta {α : Sort u} (a : α) : singl a := ⟨a, refl a⟩

def refl_contr {α : Sort u} {a b : α} (p : a ⇝ b) : LineP (λ i, a ⇝ p # i) :=
interval.hrec _ (refl a) p (begin
  cases p with f, unfold refl,
  apply heq.map, funext,
  refine interval.prop_rec _ _ i,
  { reflexivity },
  { apply ground_zero.support.truncation,
    apply eq.map, exact seg }
end)

/-
This doesn’t pass typechecking.

def J {α : Type u} {a : α} {π : Π (b : α), a ⇝ b → Type u}
  (h : π a (refl a)) (b : α) (p : a ⇝ b) : π b (<i> p # i) :=
coe (λ i, π (p # i) (conn_and p i)) h i₁

def J {α : Type u} {a : α} {π : Π (b : α), a ⇝ b → Type u}
  (h : π a (refl a)) (b : α) (p : a ⇝ b) : π b (<i> p # i) :=
transport (<i> π (p # i) (<j> p # i ∧ j)) h
-/

def J {α : Sort u} {a : α} {π : Π (b : α), a ⇝ b → Type u}
  (h : π a (refl a)) {b : α} (p : a ⇝ b) : π b p :=
trans (<i> π (p # i) (refl_contr p i)) h

def PathP (σ : I → Sort u) (a : σ i₀) (b : σ i₁) :=
Path (subst seg_path a) b

end ground_zero.cubical.path