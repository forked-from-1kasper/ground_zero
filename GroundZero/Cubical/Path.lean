import GroundZero.HITs.Interval
open GroundZero.HITs.Interval (i₀ i₁ seg)
open GroundZero.Types GroundZero.HITs
open GroundZero.Proto (idfun)

/-
  * Coercions.
  * Basic path lemmas: refl, symm, cong, funext...
  * Connections.
  * Singleton contractibility, J elimination rule.
  * PathP.
-/

namespace GroundZero.Cubical
universe u v

inductive Path (A : Type u) : A → A → Type u
| lam (f : I → A) : Path A (f 0) (f 1)

def LineP (σ : I → Type u) := Π (i : I), σ i
def Line (A : Type u) := I → A
def Line.refl {A : Type u} (a : A) : Line A := λ _, a

hott def decode {A : Type u} {a b : A} (p : a = b) : Path A a b :=
Path.lam (Interval.elim p)

hott def elim {A : Type u} {a b : A} (p : Path A a b) : I → A :=
@Path.casesOn A (λ _ _ _, I → A) a b p (@idfun (I → A))

hott def encode {A : Type u} {a b : A} (p : Path A a b) : a = b :=
@Path.casesOn A (λ a b _, a = b) a b p (Id.map · seg)

noncomputable hott def encodeDecode {A : Type u} {a b : A} (p : a = b) : encode (decode p) = p :=
by apply Interval.recβrule

hott def Path.compute {A : Type u} {a b : A} (p : Path A a b) : I → A :=
Interval.rec a b (encode p)

infix:60 " @ " => Path.compute

macro "<" is:Lean.Parser.Term.binderIdent+ ">" e:term : term =>
  Array.foldrM (λ i e, `(Path.lam (λ ($i : I), $(⟨e⟩)))) e (Array.map (λ s => ⟨s⟩) is)

namespace Path

hott def coe.forward (B : I → Type u) (i : I) (x : B i₀) : B i :=
Interval.ind x (Equiv.subst Interval.seg x) Id.refl i

hott def coe.back (B : I → Type u) (i : I) (x : B i₁) : B i :=
Interval.ind (Equiv.subst Interval.seg⁻¹ x) x (begin
  apply Id.trans; symmetry; apply Equiv.substComp;
  transitivity; apply Id.map (Equiv.subst · x);
  apply Id.invComp; reflexivity
end) i

hott def coe (i k : I) (B : I → Type u) : B i → B k :=
coe.forward (λ i, B i → B k) i (coe.forward B k)

hott def coeInv (i k : I) (B : I → Type u) : B i → B k :=
coe.back (λ i, B i → B k) i (coe.back B k)

notation "coe⁻¹" => coeInv

hott def refl {A : Type u} (a : A) : Path A a a := <_> a
instance : Reflexive (Path A) := ⟨refl⟩

hott def rfl {A : Type u} {a : A} : Path A a a := <_> a

hott def symm {A : Type u} {a b : A} (p : Path A a b) : Path A b a :=
coe 1 0 (λ i, Path A b (p @ i)) rfl

instance : Symmetric (Path A) := ⟨@symm A⟩

hott def seg : Path I i₀ i₁ := <i> i

def neg (x : I) : I := (symm seg) @ x
prefix:65 "−" => neg

example {A : Type u} {a b : A} (p : Path A a b) : Path A b a :=
<i> p @ −i

hott def homotopy {A : Type u} {B : A → Type v} (f g : Π x, B x) :=
Π x, Path (B x) (f x) (g x)
infix:50 " ~′ " => homotopy

hott def homotopyEquality {A : Type u} {B : A → Type v}
  {f g : Π x, B x} (p : f ~′ g) : f ~ g :=
λ x, encode (p x)

hott def funext {A : Type u} {B : A → Type v}
  {f g : Π x, B x} (p : f ~′ g) : Path (Π x, B x) f g :=
<i> λ x, (p x) @ i

hott def ap {A : Type u} {B : Type v} {a b : A}
  (f : A → B) (p : Path A a b) : Path B (f a) (f b) :=
<i> f (p @ i)

hott def subst {A : Type u} {B : A → Type v} {a b : A}
  (p : Path A a b) (x : B a) : B b :=
coe 0 1 (λ i, B (p @ i)) x

def transport {A : Type u} (B : A → Type v) {a b : A} (p : Path A a b) : B a → B b := subst p

section
  variable {A B : Type u} (p : Path (Type u) A B)

  hott def trans : A → B := coe 0 1 (λ i, p @ i)
  hott def transNeg : B → A := coe 1 0 (λ i, p @ i)
  hott def transBack : A → B := coe⁻¹ 0 1 (λ i, p @ i)
end

notation "trans⁻¹" => transBack

hott def transK {A B : Type u} (p : Path (Type u) A B) (x : A) :
  Path A x (transNeg p (trans p x)) :=
<i> coe i 0 (λ i, p @ i) (coe 0 i (λ i, p @ i) x)

hott def idtoeqv {A B : Type u} (p : Path (Type u) A B) : A ≃ B :=
trans (<i> A ≃ p @ i) (Equiv.ideqv A)

section
  variable {A : Type u} {a b : A} (p : Path A a b)

  hott def testEta : Path (Path A a b) p p := rfl
  hott def face₀ : A := p @ 0
  hott def face₁ : A := p @ 1

  hott def compTest₀ : Path A (p @ 0) a := rfl
  hott def compTest₁ : Path A (p @ 1) b := rfl

  -- fails, because this requires −(−i) ≡ i
  --def symmTest : Path (Path A a b) (p⁻¹)⁻¹ p := rfl
end

hott def com {A : Type u} {a b c : A} (p : Path A a b) (q : Path A b c) : Path A a c := subst q p

-- this will be replaced by a more general version in future
hott def kan {A : Type u} {a b c d : A}
  (bottom : Path A b c) (left : Path A b a) (right : Path A c d) : Path A a d :=
com (com (symm left) bottom) right

hott def kanOp {A : Type u} {a b : A} (p : Path A a a) (q : Path A a b) : Path A b b :=
kan p q q

hott def intervalContrLeft  (i : I) : Path I i₀ i := coe 0 i (Path I i₀) rfl
hott def intervalContrRight (i : I) : Path I i₁ i := coe 1 i (Path I i₁) rfl

hott def connAnd {A : Type u} {a b : A} (p : Path A a b) :
  LineP (λ i, Path A a (p @ i)) :=
λ i, <j> p @ i ∧ j

hott def connOr {A : Type u} {a b : A}
  (p : Path A a b) : LineP (λ i, Path A (p @ i) b) :=
λ i, <j> p @ i ∨ j

def singl {A : Type u} (a : A) :=
Σ (x : A), Path A a x

def eta {A : Type u} (a : A) : singl a := ⟨a, refl a⟩

@[hottAxiom] def meet {A : Type u} {a b : A} (p : Path A a b) :
  LineP (λ i, Path A a (p @ i)) :=
Interval.hrec _ (refl a) p (begin
  induction p using Path.casesOn;
  apply HEq.map lam; apply Theorems.funext;
  intro; apply Id.map; apply Interval.contrLeft
end)

/-
This doesn’t pass typechecking.

def J {A : Type u} {a : A} {C : Π (b : A), a ⇝ b → Type u}
  (h : C a (refl a)) (b : A) (p : a ⇝ b) : C b (<i> p @ i) :=
coe (λ i, C (p # i) (connAnd p i)) h i₁

def J {A : Type u} {a : A} {C : Π (b : A), a ⇝ b → Type u}
  (h : C a (refl a)) (b : A) (p : a ⇝ b) : C b (<i> p @ i) :=
transport (<i> C (p @ i) (<j> p @ i ∧ j)) h
-/

hott def J {A : Type u} {a : A} (C : Π b, Path A a b → Type v)
  (h : C a (refl a)) {b : A} (p : Path A a b) : C b p :=
trans (<i> C (p @ i) (meet p i)) h

end Path

hott def PathP (σ : I → Type u) (a : σ 0) (b : σ 1) :=
Path (σ 1) (Equiv.subst Interval.seg a) b

hott def PathP.lam (σ : I → Type u) (f : Π i, σ i) : PathP σ (f 0) (f 1) :=
Path.lam (Interval.rec _ _ (Equiv.apd f Interval.seg))

end GroundZero.Cubical