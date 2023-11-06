import GroundZero.Proto

namespace GroundZero.Types
universe u v

theorem UIP {A : Type u} {a b : A} (p q : a = b) : p = q := by rfl

section
  variable (A : Sort u)

  instance : @Reflexive A Eq  := ⟨@Eq.refl A⟩
  instance : @Symmetric A Eq  := ⟨@Eq.symm A⟩
  instance : @Transitive A Eq := ⟨@Eq.trans A⟩
end

inductive Id {A : Type u} : A → A → Type u
| idp (a : A) : Id a a

export Id (idp)

infix:50 (priority := high) " = " => Id

/- fails!
hott theorem Id.UIP {A : Type u} {a b : A} (p q : a = b) : p = q :=
begin cases p; cases q; apply idp end
-/

attribute [eliminator] Id.casesOn

hott def J₁ {A : Type u} {a : A} (B : Π (b : A), a = b → Type v)
  (Bidp : B a (idp a)) {b : A} (p : a = b) : B b p :=
@Id.casesOn A a B b p Bidp

hott def J₂ {A : Type u} {b : A} (B : Π (a : A), a = b → Type v)
  (Bidp : B b (idp b)) {a : A} (p : a = b) : B a p :=
begin induction p; apply Bidp end

namespace Id
  @[match_pattern] abbrev refl {A : Type u} {a : A} : a = a := idp a

  hott def symm {A : Type u} {a b : A} (p : a = b) : b = a :=
  begin induction p; apply idp end

  hott def trans {A : Type u} {a b c : A}
    (p : a = b) (q : b = c) : a = c :=
  begin induction p; apply q end

  instance (A : Type u) : Reflexive  (@Id A) := ⟨@idp A⟩
  instance (A : Type u) : Symmetric  (@Id A) := ⟨@symm A⟩
  instance (A : Type u) : Transitive (@Id A) := ⟨@trans A⟩

  hott def inv {A : Type u} {a b : A} (p : a = b) : b = a := symm p

  infixl:60 " ⬝ " => trans
  postfix:max "⁻¹" => symm

  hott def JSymm {A : Type} {a b : A} (B : Π x, b = x → Type v)
    (p : a = b) (w : B b (idp b)) : J₁ B w p⁻¹ = J₂ (λ x q, B x q⁻¹) w p :=
  begin induction p; reflexivity end

  hott def compInv {A : Type u} {a b : A} (p : a = b) : p ⬝ p⁻¹ = idp a :=
  begin induction p; reflexivity end

  hott def invComp {A : Type u} {a b : A} (p : a = b) : p⁻¹ ⬝ p = idp b :=
  begin induction p; reflexivity end

  hott def reflLeft {A : Type u} {a b : A} (p : a = b) : idp a ⬝ p = p :=
  begin induction p; reflexivity end

  hott def reflRight {A : Type u} {a b : A} (p : a = b) : p ⬝ idp b = p :=
  begin induction p; reflexivity end

  hott def reflTwice {A : Type u} {a b : A} (p : a = b) : idp a ⬝ p ⬝ idp b = p :=
  begin induction p; reflexivity end

  hott def explodeInv {A : Type u} {a b c : A} (p : a = b) (q : b = c) : (p ⬝ q)⁻¹ = q⁻¹ ⬝ p⁻¹ :=
  begin induction p; induction q; reflexivity end

  hott def invInv {A : Type u} {a b : A} (p : a = b) : (p⁻¹)⁻¹ = p :=
  begin induction p; reflexivity end

  hott def invEqIfEqInv {A : Type u} {a b : A} {p : a = b} {q : b = a} : p⁻¹ = q → p = q⁻¹ :=
  begin induction p; intro η; induction η; reflexivity end

  hott def eqEnvIfInvEq {A : Type u} {a b : A} {p : a = b} {q : b = a} : p = q⁻¹ → p⁻¹ = q :=
  λ η => @invEqIfEqInv A b a p⁻¹ q⁻¹ (invInv p ⬝ η) ⬝ invInv q

  hott def assoc {A : Type u} {a b c d : A} (p : a = b) (q : b = c) (r : c = d) :
    p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r :=
  begin induction p; reflexivity end

  hott def mpr {A B : Type u} (p : A = B) : B → A :=
  begin induction p; intro x; exact x end

  hott def ap {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : a = b) : f a = f b :=
  begin induction p; reflexivity end

  hott def cancelCompInv {A : Type u} {a b c : A} (p : a = b) (q : b = c) : (p ⬝ q) ⬝ q⁻¹ = p :=
  (assoc p q q⁻¹)⁻¹ ⬝ ap (trans p) (compInv q) ⬝ reflRight p

  hott def cancelInvComp {A : Type u} {a b c : A} (p : a = b) (q : c = b) : (p ⬝ q⁻¹) ⬝ q = p :=
  (assoc p q⁻¹ q)⁻¹ ⬝ ap (trans p) (invComp q) ⬝ reflRight p

  hott def compInvCancel {A : Type u} {a b c : A} (p : a = b) (q : a = c) : p ⬝ (p⁻¹ ⬝ q) = q :=
  assoc p p⁻¹ q ⬝ ap (· ⬝ q) (compInv p)

  hott def invCompCancel {A : Type u} {a b c : A} (p : a = b) (q : b = c) : p⁻¹ ⬝ (p ⬝ q) = q :=
  assoc p⁻¹ p q ⬝ ap (· ⬝ q) (invComp p)

  hott def mapInv {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : a = b) : ap f p⁻¹ = (ap f p)⁻¹ :=
  begin induction p; reflexivity end

  hott def transCancelLeft {A : Type u} {a b c : A}
    (r : a = b) (p q : b = c) : r ⬝ p = r ⬝ q → p = q :=
  begin intro μ; induction r; exact μ end

  hott def transCancelRight {A : Type u} {a b c : A} (r : b = c) (p q : a = b) : p ⬝ r = q ⬝ r → p = q :=
  begin
    intro μ; induction r; transitivity; { symmetry; apply reflRight };
    symmetry; transitivity; { symmetry; apply reflRight }; exact μ⁻¹
  end

  section
    variable {A : Type u} {B : Type v} {a b : A} {p q : a = b}

    hott def ap₂ (f : A → B) (r : p = q) : ap f p = ap f q :=
    ap (ap f) r

    hott def ap₃ {α β : p = q} (f : A → B) (r : α = β) : ap₂ f α = ap₂ f β :=
    ap (ap₂ f) r
  end

  hott def compReflIfEq {A : Type u} {a b : A} (p q : a = b) : p = q → p⁻¹ ⬝ q = idp b :=
  begin intro A; induction A; apply invComp end

  hott def eqIfCompRefl {A : Type u} {a b : A} (p q : a = b) : p⁻¹ ⬝ q = idp b → p = q :=
  begin intro α; induction p; exact α⁻¹ end

  class isPointed (A : Type u) := (point : A)

  hott def pointOf (A : Type u) [isPointed A] : A := isPointed.point

  hott def Pointed := Σ (A : Type u), A

  macro "Type⁎" : term => `(Pointed)
  macro "Type⁎" n:level : term => `(Pointed.{$n})

  abbrev Pointed.space : Type⁎ u → Type u := Sigma.fst
  abbrev Pointed.point : Π (A : Type⁎ u), A.space := Sigma.snd

  def Pointed.Map (A B : Type⁎) :=
  Σ (f : A.space → B.space), f A.point = B.point

  notation "Map⁎" => Pointed.Map

  namespace Pointed.Map
    variable {A B : Type⁎} (φ : Map⁎ A B)

    def ap : A.space → B.space := φ.fst
    def id : φ.ap A.point = B.point := φ.snd
  end Pointed.Map

  hott def Loop {B : Type u} (b : B) : ℕ → Type u
  | Nat.zero   => B
  | Nat.succ n => Loop (idp b) n

  macro:max "Ω" n:superscript "(" τ:term ")" : term => do
    `(Loop (pointOf $τ) $(← Meta.Notation.parseSuperscript n))

  macro:max "Ω" n:superscript "(" τ:term "," ε:term ")" : term => do
    `(@Loop $τ $ε $(← Meta.Notation.parseSuperscript n))

  macro:max "Ω" "[" n:term "]" "(" τ:term ")" : term => do
    `(Loop (pointOf $τ) $n)

  macro:max "Ω" "[" n:term "]" "(" τ:term "," ε:term ")" : term => do
    `(@Loop $τ $ε $n)

  hott def idloop {B : Type u} (b : B) : Π n, Ωⁿ(B, b)
  | Nat.zero   => b
  | Nat.succ n => idloop (idp b) n

  hott def aploop {A : Type u} {B : Type v} (f : A → B) {a : A} : Π {n : ℕ}, Ωⁿ(A, a) → Ωⁿ(B, f a)
  | Nat.zero   => f
  | Nat.succ _ => aploop (ap f)
end Id

def Not (A : Type u) : Type u := A → (𝟎 : Type)
def Neq {A : Type u} (a b : A) := Not (Id a b)

namespace Not
  prefix:90 (priority := high) "¬" => Not
  infix:50 (priority := high) " ≠ " => Neq

  def absurd {A : Type u} {B : Type v} (h : A) (g : ¬A) : B :=
  nomatch (g h)

  def univ : (𝟎 : Type u) → (𝟎 : Type v) :=
  λ e, nomatch e
end Not

namespace Whiskering
  open GroundZero.Types.Id (ap)

  variable {A : Type u} {a b c : A}

  hott def rwhs {p q : a = b} (ν : p = q) (r : b = c) : p ⬝ r = q ⬝ r :=
  begin induction r; apply (Id.reflRight p) ⬝ ν ⬝ (Id.reflRight q)⁻¹ end

  infix:60 " ⬝ᵣ " => rwhs

  hott def lwhs {r s : b = c} (q : a = b) (κ : r = s) : q ⬝ r = q ⬝ s :=
  begin induction q; exact (Id.reflLeft r) ⬝ κ ⬝ (Id.reflLeft s)⁻¹ end

  infix:60 " ⬝ₗ " => lwhs

  variable {p q : a = b} {r s : b = c}

  hott def horizontalComp₁ (ν : p = q) (κ : r = s) := (ν ⬝ᵣ r) ⬝ (q ⬝ₗ κ)
  infix:65 " ⋆ " => horizontalComp₁

  hott def horizontalComp₂ (ν : p = q) (κ : r = s) := (p ⬝ₗ κ) ⬝ (ν ⬝ᵣ s)
  infix:65 " ⋆′ " => horizontalComp₂

  hott lemma compUniq (ν : p = q) (κ : r = s) : ν ⋆ κ = ν ⋆′ κ :=
  begin induction p; induction r; induction ν; induction κ; reflexivity end

  hott lemma loop₁ {A : Type u} {a : A} {ν κ : idp a = idp a} : ν ⬝ κ = ν ⋆ κ :=
  begin
    apply Id.symm; transitivity; apply ap (· ⬝ _);
    apply Id.reflTwice; apply ap (ν ⬝ ·); apply Id.reflTwice
  end

  hott lemma loop₂ {A : Type u} {a : A} {ν κ : idp a = idp a} : ν ⋆′ κ = κ ⬝ ν :=
  begin
    transitivity; apply ap (· ⬝ _); apply Id.reflTwice;
    apply ap (κ ⬝ ·); apply Id.reflTwice
  end

  hott theorem «Eckmann–Hilton argument» {A : Type u} {a : A}
    (ν κ : idp a = idp a) : ν ⬝ κ = κ ⬝ ν :=
  loop₁ ⬝ compUniq ν κ ⬝ loop₂

  hott corollary comm {A : Type u} {a b : A} {p : a = b} (ν κ : p = p) : ν ⬝ κ = κ ⬝ ν :=
  begin induction p; apply «Eckmann–Hilton argument» end
end Whiskering

end GroundZero.Types
