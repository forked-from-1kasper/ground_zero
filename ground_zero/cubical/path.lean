import ground_zero.cubical.cubes
open ground_zero.cubical.cubes ground_zero.types ground_zero.HITs
open ground_zero.HITs.interval (i₀ i₁ seg)

namespace ground_zero.cubical.path
universes u v

@[refl] def refl {α : Type u} (a : α) : a ⇝ a := <i> a
@[refl] def rfl {α : Type u} {a : α} : a ⇝ a := <i> a

@[symm] def symm {α : Type u} {a b : α} (p : a ⇝ b) : b ⇝ a :=
<i> p # −i
postfix `⁻¹` := symm

def funext {α : Type u} {β : α → Type v} {f g : Π (x : α), β x}
  (p : Π (x : α), f x ⇝ g x) : f ⇝ g :=
<i> λ x, (p x) # i

def cong {α : Type u} {β : Type v} {a b : α}
  (f : α → β) (p : a ⇝ b) : f a ⇝ f b :=
<i> f (p # i)

def subst {α : Type u} {π : α → Type v} {a b : α}
  (p : a ⇝ b) (x : π a) : π b :=
coe (λ i, π (p # i)) x i₁

abbreviation transport {α : Type u} (π : α → Type v) {a b : α}
  (p : a ⇝ b) : π a → π b := subst p

def transportconst {α β : Type u} : (α ⇝ β) → (α → β) :=
transport id

def idtoeqv {α β : Type u} (p : α ⇝ β) : α ≃ β :=
transportconst (<i> α ≃ p # i) (equiv.id α)

def test_eta {α : Type u} {a b : α} (p : a ⇝ b) : p ⇝ p := rfl
def face₀ {α : Type u} {a b : α} (p : a ⇝ b) : α := p # i₀
def face₁ {α : Type u} {a b : α} (p : a ⇝ b) : α := p # i₁

def comp_test₀ {α : Type u} {a b : α} (p : a ⇝ b) : (p # i₀) ⇝ a := rfl
def comp_test₁ {α : Type u} {a b : α} (p : a ⇝ b) : (p # i₁) ⇝ b := rfl

-- fail
--def symm_test {α : Type u} {a b : α} (p : a ⇝ b) : (p⁻¹)⁻¹ ⇝ p := rfl
@[trans] def trans {α : Type u} {a b c : α}
  (p : a ⇝ b) (q : b ⇝ c) : a ⇝ c := subst q p

infix ⬝ := trans

-- this will be replaced by a more general version in future
def comp {α : Type u} {a b c d : α}
  (bottom : b ⇝ c) (left : b ⇝ a) (right : c ⇝ d) : a ⇝ d :=
left⁻¹ ⬝ bottom ⬝ right

def interval_contr (i : I) : i₀ ⇝ i := coe (λ i, i₀ ⇝ i) rfl i
def seg_path : i₀ ⇝ i₁ := interval_contr i₁

def conn_and {α : Sort u} {a b : α} (p : a ⇝ b) :
  LineP (λ i, a ⇝ p # i) :=
λ i, <j> p # i ∧ j

def PathP (σ : I → Type u) (a : σ i₀) (b : σ i₁) :=
Path (subst seg_path a) b

/-
This doesn’t pass typechecking.

def J {α : Type u} {a : α} {π : Π (b : α), a ⇝ b → Type u}
  (h : π a (refl a)) (b : α) (p : a ⇝ b) : π b (<i> p # i) :=
coe (λ i, π (p # i) (conn_and p i)) h i₁

def J {α : Type u} {a : α} {π : Π (b : α), a ⇝ b → Type u}
  (h : π a (refl a)) (b : α) (p : a ⇝ b) : π b (<i> p # i) :=
transport (<i> π (p # i) (<j> p # i ∧ j)) h
-/

-- dirty way to define J elimination rule
def hrec {β : I → Sort u}
  (b₀ : β i₀) (b₁ : β i₁) (s : b₀ == b₁)
  (x : I) : β x :=
@quot.hrec_on bool (λ _ _, true) β x
  (λ i, bool.rec_on i b₀ b₁)
  (λ a b _,
    begin simp, induction a; induction b; simp,
          apply s, symmetry, apply s end)

def J {α : Type u} {a : α} {π : Π (b : α), a ⇝ b → Type u}
  (h : π a (refl a)) {b : α} (p : a ⇝ b) : π b p :=
let dsingl : LineP (λ i, a ⇝ p # i) :=
hrec (refl a) p (begin
  cases p with f, unfold refl,
  apply heq.map, funext,
  refine interval.hrec _ _ i,
  { reflexivity },
  { apply ground_zero.support.truncation,
    apply eq.map, exact seg }
end) in
transportconst (<i> π (p # i) (dsingl i)) h

end ground_zero.cubical.path