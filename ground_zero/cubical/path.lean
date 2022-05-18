import ground_zero.HITs.interval
open ground_zero.HITs.interval (i₀ i₁ seg)
open ground_zero.types ground_zero.HITs
open ground_zero.proto (idfun)

/-
  * Coercions.
  * Basic path lemmas: refl, symm, cong, funext...
  * Connections.
  * Singleton contractibility, J elimination rule.
  * PathP.
-/

hott theory

namespace ground_zero.cubical
universes u v

inductive Path (A : Type u) : A → A → Type u
| lam (f : I → A) : Path (f 0) (f 1)

def LineP (σ : I → Type u) := Π (i : I), σ i
def Line (α : Type u) := I → α
def Line.refl {α : Type u} (a : α) : Line α := λ _, a

@[hott] def decode {A : Type u} {a b : A} (p : a = b) : Path A a b :=
Path.lam (interval.elim p)

@[hott] def elim {A : Type u} {a b : A} (p : Path A a b) : I → A :=
Path.rec (@idfun (I → A)) p

@[hott] def encode {A : Type u} {a b : A} (p : Path A a b) : a = b :=
Path.rec (# seg) p

@[hott] noncomputable def encode_decode {A : Type u} {a b : A} (p : a = b) :
  encode (decode p) = p :=
by apply interval.recβrule

@[hott] def Path.compute {A : Type u} {a b : A} (p : Path A a b) : I → A :=
interval.rec a b (encode p)

infix ` # `:60 := Path.compute
notation `<` binder `> ` r:(scoped P, Path.lam P) := r

namespace Path

@[hott] def coe.forward (π : I → Type u) (i : I) (x : π i₀) : π i :=
interval.ind x (equiv.subst interval.seg x) Id.refl i

@[hott] def coe.back (π : I → Type u) (i : I) (x : π i₁) : π i :=
interval.ind (equiv.subst interval.seg⁻¹ x) x (begin
  apply Id.trans,
  { symmetry, apply equiv.subst_comp }, transitivity,
  { apply Id.map (λ p, equiv.subst p x), apply Id.inv_comp },
  reflexivity
end) i

@[hott] def coe (i k : I) (π : I → Type u) : π i → π k :=
coe.forward (λ i, π i → π k) i (coe.forward π k)

@[hott] def coe_inv (i k : I) (π : I → Type u) : π i → π k :=
coe.back (λ i, π i → π k) i (coe.back π k)

notation `coe⁻¹` := coe_inv

@[hott, refl] def refl {A : Type u} (a : A) : Path A a a := <i> a
@[hott] def rfl {A : Type u} {a : A} : Path A a a := <i> a

@[hott, symm] def symm {A : Type u} {a b : A} (p : Path A a b) : Path A b a :=
coe 1 0 (λ i, Path A b (p # i)) rfl
postfix `⁻¹` := symm

@[hott] def seg : Path I i₀ i₁ := <i> i

def neg (x : I) : I := seg⁻¹ # x
prefix `−`:30 := neg

example {A : Type u} {a b : A} (p : Path A a b) : Path A b a :=
<i> p # −i

def homotopy {A : Type u} {B : A → Type v} (f g : Π (x : A), B x) :=
Π (x : A), Path (B x) (f x) (g x)
infix ` ~' `:50 := homotopy

@[hott] def homotopy_equality {α : Type u} {π : α → Type v}
  {f g : Π (x : α), π x} (p : f ~' g) : f ~ g :=
λ x, encode (p x)

@[hott] def funext {A : Type u} {B : A → Type v} {f g : Π x, B x}
  (p : f ~' g) : Path (Π x, B x) f g :=
<i> λ x, p x # i

@[hott] def ap {A : Type u} {B : Type v} {a b : A}
  (f : A → B) (p : Path A a b) : Path B (f a) (f b) :=
<i> f (p # i)

@[hott] def subst {A : Type u} {B : A → Type v} {a b : A}
  (p : Path A a b) (x : B a) : B b :=
coe 0 1 (λ i, B (p # i)) x

def transport {A : Type u} (B : A → Type v) {a b : A} (p : Path A a b) : B a → B b := subst p

section
  variables {A B : Type u} (p : Path Type* A B)

  @[hott] def trans : A → B := coe 0 1 (λ i, p # i)
  @[hott] def trans_neg : B → A := coe 1 0 (λ i, p # i)
  @[hott] def trans_back : A → B := coe⁻¹ 0 1 (λ i, p # i)
end

notation `trans⁻¹` := trans_back

@[hott] def transK {A B : Type u} (p : Path Type* A B) (x : A) :
  Path A x (trans_neg p (trans p x)) :=
<i> coe i 0 (λ i, p # i) (coe 0 i (λ i, p # i) x)

@[hott] def idtoeqv {A B : Type u} (p : Path Type* A B) : A ≃ B :=
trans (<i> A ≃ p # i) (equiv.id A)

section
  variables {A : Type u} {a b : A} (p : Path A a b)

  @[hott] def test_eta : Path (Path A a b) p p := rfl
  @[hott] def face₀ : A := p # 0
  @[hott] def face₁ : A := p # 1

  @[hott] def comp_test₀ : Path A (p # 0) a := rfl
  @[hott] def comp_test₁ : Path A (p # 1) b := rfl

  -- fails, because this requires −(−i) ≡ i
  --def symm_test : Path (Path A a b) (p⁻¹)⁻¹ p := rfl
end

@[hott, trans] def com {A : Type u} {a b c : A}
  (p : Path A a b) (q : Path A b c) : Path A a c := subst q p

infix ` ⬝ ` := com

-- this will be replaced by a more general version in future
@[hott] def kan {A : Type u} {a b c d : A}
  (bottom : Path A b c) (left : Path A b a) (right : Path A c d) : Path A a d :=
left⁻¹ ⬝ bottom ⬝ right

@[hott] def kan_op {A : Type u} {a b : A} (p : Path A a a) (q : Path A a b) : Path A b b :=
kan p q q

@[hott] def interval_contr_left  (i : I) : Path I i₀ i := coe 0 i (Path I i₀) rfl
@[hott] def interval_contr_right (i : I) : Path I i₁ i := coe 1 i (Path I i₁) rfl

@[hott] def conn_and {A : Type u} {a b : A} (p : Path A a b) :
  LineP (λ i, Path A a (p # i)) :=
λ i, <j> p # i ∧ j

@[hott] def conn_or {A : Type u} {a b : A}
  (p : Path A a b) : LineP (λ i, Path A (p # i) b) :=
λ i, <j> p # i ∨ j

def singl {A : Type u} (a : A) :=
Σ (x : A), Path A a x

def eta {A : Type u} (a : A) : singl a := ⟨a, refl a⟩

@[hott] noncomputable def transport_correct {A : Type u} {B : A → Type v}
  {a b : A} (p : a = b) (x : B a) : transport B (decode p) x = equiv.transport B p x :=
begin
  induction p, transitivity, apply equiv.transport_comp,
  transitivity, apply Id.map (λ p, equiv.transport B p x),
  { transitivity, iterate 2 { apply interval.recβrule } }, reflexivity
end

@[safe] def meet {A : Type u} {a b : A} (p : Path A a b) :
  LineP (λ i, Path A a (p # i)) :=
interval.hrec _ (refl a) p (begin
  cases p with φ, apply heq.map lam, funext,
  refine interval.prop_rec _ _ i,
  { reflexivity },
  { apply ground_zero.support.truncation,
    apply Id.map, exact interval.seg }
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

@[hott] def J {A : Type u} {a : A} (C : Π b, Path A a b → Type v)
  (h : C a (refl a)) {b : A} (p : Path A a b) : C b p :=
trans (<i> C (p # i) (meet p i)) h

end Path

@[hott] def PathP (σ : I → Type u) (a : σ 0) (b : σ 1) :=
Path (σ 1) (equiv.subst interval.seg a) b

@[hott] def PathP.lam (σ : I → Type u) (f : Π i, σ i) : PathP σ (f 0) (f 1) :=
Path.lam (interval.rec _ _ (equiv.apd f interval.seg))

end ground_zero.cubical