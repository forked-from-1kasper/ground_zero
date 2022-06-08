import GroundZero.Proto

namespace GroundZero.Types
universe u v

theorem UIP {A : Type u} {a b : A} (p q : a = b) : p = q :=
begin rfl end

section
  variable (A : Sort u)

  instance : @Reflexive A Eq  := ⟨@Eq.refl A⟩
  instance : @Symmetric A Eq  := ⟨@Eq.symm A⟩
  instance : @Transitive A Eq := ⟨@Eq.trans A⟩
end

inductive Id {A : Type u} : A → A → Type u
| refl {a : A} : Id a a

infix:50 (priority := high) " = " => Id

/- fails!
hott theorem Id.UIP {A : Type u} {a b : A} (p q : a = b) : p = q :=
begin cases p; cases q; apply Id.refl end
-/

@[matchPattern] abbrev idp {A : Type u} (a : A) : a = a := Id.refl

namespace Id
  attribute [eliminator] Id.casesOn

  hott def symm {A : Type u} {a b : A} (p : a = b) : b = a :=
  begin induction p; apply idp end

  hott def trans {A : Type u} {a b c : A}
    (p : a = b) (q : b = c) : a = c :=
  begin induction p; apply q end

  instance : Reflexive  (@Id A) := ⟨@Id.refl A⟩
  instance : Symmetric  (@Id A) := ⟨@symm A⟩
  instance : Transitive (@Id A) := ⟨@trans A⟩

  hott def inv {A : Type u} {a b : A} (p : a = b) : b = a := symm p

  infixl:60 " ⬝ " => trans
  postfix:max "⁻¹" => symm

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

  hott def assoc {A : Type u} {a b c d : A}
    (p : a = b) (q : b = c) (r : c = d) :
    p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r :=
  begin induction p; reflexivity end

  hott def mpr {A B : Type u} (p : A = B) : B → A :=
  begin induction p; intro x; exact x end

  hott def map {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : a = b) : f a = f b :=
  begin induction p; reflexivity end

  hott def cancelCompInv {A : Type u} {a b c : A} (p : a = b) (q : b = c) : (p ⬝ q) ⬝ q⁻¹ = p :=
  (assoc p q q⁻¹)⁻¹ ⬝ map (trans p) (compInv q) ⬝ (reflRight p)

  hott def cancelInvComp {A : Type u} {a b c : A} (p : a = b) (q : c = b) : (p ⬝ q⁻¹) ⬝ q = p :=
  (assoc p q⁻¹ q)⁻¹ ⬝ map (trans p) (invComp q) ⬝ (reflRight p)

  hott def mapInv {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : a = b) : map f p⁻¹ = (map f p)⁻¹ :=
  begin induction p; reflexivity end

  hott def transCancelLeft {A : Type u} {a b c : A}
    (r : a = b) (p q : b = c) : r ⬝ p = r ⬝ q → p = q :=
  begin intro μ; induction r; exact μ end

  hott def transCancelRight {A : Type u} {a b c : A}
    (r : b = c) (p q : a = b) : p ⬝ r = q ⬝ r → p = q :=
  begin
    intro μ; induction r; transitivity; { symmetry; apply reflRight };
    symmetry; transitivity; { symmetry; apply reflRight }; exact μ⁻¹
  end

  hott def idConjIfComm {A : Type u} {a : A}
    (p q : a = a) : p ⬝ q = q ⬝ p → q⁻¹ ⬝ p ⬝ q = p :=
  begin
    intro r; apply transCancelLeft q;
    transitivity; apply assoc;
    transitivity; apply map (· ⬝ q);
    transitivity; apply assoc; apply map (· ⬝ p);
    apply compInv; exact r
  end

  hott def compReflIfEq {A : Type u} {a b : A} (p q : a = b) : p = q → p⁻¹ ⬝ q = idp b :=
  begin intro A; induction A; apply invComp end

  section
    variable {A : Type u} {B : Type v} {a b : A} (f : A → B) (p : a = b)

    def cong := map f p
    def ap   := map f p
  end

  hott def ap₂ {A : Type u} {B : Type v} {a b : A} {p q : a = b}
    (f : A → B) (r : p = q) : ap f p = ap f q :=
  ap (ap f) r

  class dotted (space : Type u) :=
  (point : space)

  structure pointed :=
  (space : Type u) (point : space)

  notation "Type⁎" => pointed

  def pointed.map (A B : Type⁎) :=
  Σ (f : A.space → B.space), f A.point = B.point
  notation "Map⁎" => pointed.map

  namespace pointed.map
    variable {A B : Type⁎} (φ : Map⁎ A B)

    def ap : A.space → B.space := φ.fst
    def id : φ.ap A.point = B.point := φ.snd
  end pointed.map

  def loopSpace (X : Type⁎) : Type⁎ :=
  ⟨X.point = X.point, Id.refl⟩

  hott def iteratedLoopSpace : Type⁎ → ℕ → Type⁎
  | X,   0   => X
  | X, n + 1 => iteratedLoopSpace (loopSpace X) n

  def loopPointedSpace (A : Type u) [dotted A] :=
  iteratedLoopSpace ⟨A, dotted.point⟩

  macro:max "Ω" n:superscript "(" τ:term ")" : term => do
    `((loopPointedSpace $τ $(← Meta.Notation.parseSuperscript n)).space)

  macro:max "Θ" n:superscript "(" τ:term ")" : term => do
    `((iteratedLoopSpace $τ $(← Meta.Notation.parseSuperscript n)).point)
end Id

def Not (A : Type u) : Type u := A → (𝟎 : Type)
def Neq {A : Type u} (a b : A) := Not (Id a b)

namespace Not
  prefix:90 (priority := high) "¬" => Not
  infix:50 (priority := high) " ≠ " => Neq

  def absurd {A : Type u} {B : Type v} (h : A) (g : ¬A) : B :=
  GroundZero.Proto.Empty.casesOn (λ _, B) (g h)

  def univ : (𝟎 : Type u) → (𝟎 : Type v) :=
  λ e, nomatch e
end Not

namespace whiskering
  variable {A : Type u} {a b c : A}

  hott def rightWhs (ν : p = q) (r : b = c) : p ⬝ r = q ⬝ r :=
  begin induction r; apply (Id.reflRight p) ⬝ ν ⬝ (Id.reflRight q)⁻¹ end

  infix:60 " ⬝ᵣ " => rightWhs

  hott def leftWhs (q : a = b) (κ : r = s) : q ⬝ r = q ⬝ s :=
  begin induction q; exact (Id.reflLeft r) ⬝ κ ⬝ (Id.reflLeft s)⁻¹ end

  infix:60 " ⬝ₗ " => leftWhs

  variable {p q : a = b} {r s : b = c}

  hott def horizontalComp₁ (ν : p = q) (κ : r = s) := (ν ⬝ᵣ r) ⬝ (q ⬝ₗ κ)
  infix:65 " ⋆ " => horizontalComp₁

  hott def horizontalComp₂ (ν : p = q) (κ : r = s) := (p ⬝ₗ κ) ⬝ (ν ⬝ᵣ s)
  infix:65 " ⋆′ " => horizontalComp₂

  hott def compUniq (ν : p = q) (κ : r = s) : ν ⋆ κ = ν ⋆′ κ :=
  begin induction p; induction r; induction ν; induction κ; reflexivity end

  hott def loop₁ {A : Type u} {a : A} {ν κ : idp a = idp a} : ν ⬝ κ = ν ⋆ κ :=
  begin
    apply Id.symm; transitivity;
    { apply Id.map (· ⬝ (Id.refl ⬝ κ ⬝ Id.refl));
      apply Id.reflTwice };
    apply Id.map (ν ⬝ ·); apply Id.reflTwice
  end

  hott def loop₂ {A : Type u} {a : A} {ν κ : idp a = idp a} : ν ⋆′ κ = κ ⬝ ν :=
  begin
    transitivity;
    { apply Id.map (· ⬝ (Id.refl ⬝ ν ⬝ Id.refl));
      apply Id.reflTwice };
    apply Id.map (κ ⬝ ·); apply Id.reflTwice
  end

  hott def «Eckmann–Hilton argument» {A : Type u} {a : A}
    (ν κ : idp a = idp a) : ν ⬝ κ = κ ⬝ ν :=
  loop₁ ⬝ compUniq ν κ ⬝ loop₂
end whiskering

end GroundZero.Types