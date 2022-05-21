import GroundZero.Meta.HottTheory
import GroundZero.Proto

namespace GroundZero.Types
universe u v

theorem UIP {α : Type u} {a b : α} (p q : a = b) : p = q :=
begin rfl end

inductive Id {α : Type u} : α → α → Type u
| refl {a : α} : Id a a

def Eq (α : Type u) (a b : α) := Id a b

infix:50 (priority := high) " = " => Id

/- fails!
hott theorem Id.UIP {α : Type u} {a b : α} (p q : a = b) : p = q :=
begin cases p; cases q; apply Id.refl end
-/

abbrev idp {α : Type u} (a : α) : a = a := Id.refl

namespace Id
  attribute [eliminator] Id.casesOn

  hott def symm {α : Type u} {a b : α} (p : a = b) : b = a :=
  begin induction p; apply idp end

  hott def trans {α : Type u} {a b c : α}
    (p : a = b) (q : b = c) : a = c :=
  begin induction p; apply q end

  instance : Reflexive  (Eq α) := ⟨Id.refl⟩
  instance : Symmetric  (Eq α) := ⟨symm⟩
  instance : Transitive (Eq α) := ⟨trans⟩

  instance {α : Type u} : @Reflexive α  (· = ·) := ⟨Id.refl⟩
  instance {α : Type u} : @Symmetric α  (· = ·) := ⟨symm⟩
  instance {α : Type u} : @Transitive α (· = ·) := ⟨trans⟩

  hott def inv {α : Type u} {a b : α} (p : a = b) : b = a := symm p

  infixl:60 " ⬝ " => trans
  postfix:max "⁻¹" => symm

  hott def compInv {α : Type u} {a b : α} (p : a = b) : p ⬝ p⁻¹ = idp a :=
  begin induction p; reflexivity end

  hott def invComp {α : Type u} {a b : α} (p : a = b) : p⁻¹ ⬝ p = idp b :=
  begin induction p; reflexivity end

  hott def reflLeft {α : Type u} {a b : α} (p : a = b) : idp a ⬝ p = p :=
  begin induction p; reflexivity end

  hott def reflRight {α : Type u} {a b : α} (p : a = b) : p ⬝ idp b = p :=
  begin induction p; reflexivity end

  hott def reflTwice {α : Type u} {a b : α} (p : a = b) : idp a ⬝ p ⬝ idp b = p :=
  begin induction p; reflexivity end

  hott def explodeInv {α : Type u} {a b c : α} (p : a = b) (q : b = c) : (p ⬝ q)⁻¹ = q⁻¹ ⬝ p⁻¹ :=
  begin induction p; induction q; reflexivity end

  hott def invInv {α : Type u} {a b : α} (p : a = b) : (p⁻¹)⁻¹ = p :=
  begin induction p; reflexivity end

  hott def invEqIfEqInv {α : Type u} {a b : α} {p : a = b} {q : b = a} : p⁻¹ = q → p = q⁻¹ :=
  begin induction p; intro η; induction η; reflexivity end

  hott def eqEnvIfInvEq {α : Type u} {a b : α} {p : a = b} {q : b = a} : p = q⁻¹ → p⁻¹ = q :=
  λ η => @invEqIfEqInv α b a p⁻¹ q⁻¹ (invInv p ⬝ η) ⬝ invInv q

  hott def assoc {α : Type u} {a b c d : α}
    (p : a = b) (q : b = c) (r : c = d) :
    p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r :=
  begin induction p; reflexivity end

  hott def mpr {α β : Type u} (p : α = β) : β → α :=
  begin induction p; intro x; exact x end

  hott def map {α : Type u} {β : Type v} {a b : α}
    (f : α → β) (p : a = b) : f a = f b :=
  begin induction p; reflexivity end

  hott def cancelCompInv {α : Type u} {a b c : α} (p : a = b) (q : b = c) : (p ⬝ q) ⬝ q⁻¹ = p :=
  (assoc p q q⁻¹)⁻¹ ⬝ map (trans p) (compInv q) ⬝ (reflRight p)

  hott def cancelInvComp {α : Type u} {a b c : α} (p : a = b) (q : c = b) : (p ⬝ q⁻¹) ⬝ q = p :=
  (assoc p q⁻¹ q)⁻¹ ⬝ map (trans p) (invComp q) ⬝ (reflRight p)

  hott def mapInv {α : Type u} {β : Type v} {a b : α}
    (f : α → β) (p : a = b) : map f p⁻¹ = (map f p)⁻¹ :=
  begin induction p; reflexivity end

  hott def transCancelLeft {α : Type u} {a b c : α}
    (r : a = b) (p q : b = c) : r ⬝ p = r ⬝ q → p = q :=
  begin intro μ; induction r; exact μ end

  hott def transCancelRight {α : Type u} {a b c : α}
    (r : b = c) (p q : a = b) : p ⬝ r = q ⬝ r → p = q :=
  begin
    intro μ; induction r; transitivity; { symmetry; apply reflRight };
    symmetry; transitivity; { symmetry; apply reflRight }; exact μ⁻¹
  end

  hott def idConjIfComm {α : Type u} {a : α}
    (p q : a = a) : p ⬝ q = q ⬝ p → q⁻¹ ⬝ p ⬝ q = p :=
  begin
    intro r; apply transCancelLeft q;
    transitivity; apply assoc;
    transitivity; apply map (· ⬝ q);
    transitivity; apply assoc; apply map (· ⬝ p);
    apply compInv; exact r
  end

  hott def compReflIfEq {α : Type u} {a b : α} (p q : a = b) : p = q → p⁻¹ ⬝ q = idp b :=
  begin intro α; induction α; apply invComp end

  section
    variable {α : Type u} {β : Type v} {a b : α} (f : α → β) (p : a = b)

    def cong := map f p
    def ap   := map f p
  end

  hott def ap₂ {α : Type u} {β : Type v} {a b : α}
    {p q : a = b} (f : α → β) (r : p = q) : ap f p = ap f q :=
  begin induction r; reflexivity end

  class dotted (space : Type u) :=
  (point : space)

  structure pointed :=
  (space : Type u) (point : space)

  notation "Type⁎" => pointed

  def pointed.map (α β : Type⁎) :=
  Σ (f : α.space → β.space), f α.point = β.point
  notation "Map⁎" => pointed.map

  namespace pointed.map
    variable {α β : Type⁎} (φ : Map⁎ α β)

    def ap : α.space → β.space := φ.fst
    def id : φ.ap α.point = β.point := φ.snd
  end pointed.map

  def loopSpace (X : Type⁎) : Type⁎ :=
  ⟨X.point = X.point, Id.refl⟩

  hott def iteratedLoopSpace : Type⁎ → ℕ → Type⁎
  | X,   0   => X
  | X, n + 1 => iteratedLoopSpace (loopSpace X) n

  def loopPointedSpace (α : Type u) [dotted α] :=
  iteratedLoopSpace ⟨α, dotted.point⟩

  macro "Ω" n:many1(superscriptNumeral) τ:term : term =>
    `((iteratedLoopSpace $τ $(Meta.Notation.parseNumber n)).space)

  macro "Ω" i:many1(superscriptChar) τ:term : term =>
    `((iteratedLoopSpace $τ $(Lean.mkIdent (Meta.Notation.parseIdent i))).space)

  macro "Θ" n:many1(superscriptNumeral) τ:term : term =>
    `((iteratedLoopSpace $τ $(Meta.Notation.parseNumber n)).point)

  macro "Θ" i:many1(superscriptChar) τ:term : term =>
    `((iteratedLoopSpace $τ $(Lean.mkIdent (Meta.Notation.parseIdent i))).point)
end Id

def not (α : Type u) : Type u := α → (𝟎 : Type)
def neq {α : Type u} (a b : α) := not (Id a b)

namespace not
  prefix:90 (priority := high) "¬" => not
  infix:50 (priority := high) " ≠ " => neq

  def absurd {α : Type u} {β : Type v} (h : α) (g : ¬α) : β :=
  GroundZero.Proto.Empty.casesOn (λ _, β) (g h)

  def univ : (𝟎 : Type u) → (𝟎 : Type v) :=
  λ e, nomatch e
end not

namespace whiskering
  variable {α : Type u} {a b c : α}

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

  hott def loop₁ {α : Type u} {a : α} {ν κ : idp a = idp a} : ν ⬝ κ = ν ⋆ κ :=
  begin
    apply Id.symm; transitivity;
    { apply Id.map (· ⬝ (Id.refl ⬝ κ ⬝ Id.refl));
      apply Id.reflTwice };
    apply Id.map (ν ⬝ ·); apply Id.reflTwice
  end

  hott def loop₂ {α : Type u} {a : α} {ν κ : idp a = idp a} : ν ⋆′ κ = κ ⬝ ν :=
  begin
    transitivity;
    { apply Id.map (· ⬝ (Id.refl ⬝ ν ⬝ Id.refl));
      apply Id.reflTwice };
    apply Id.map (κ ⬝ ·); apply Id.reflTwice
  end

  hott def «Eckmann–Hilton argument» {α : Type u} {a : α}
    (ν κ : idp a = idp a) : ν ⬝ κ = κ ⬝ ν :=
  loop₁ ⬝ compUniq ν κ ⬝ loop₂
end whiskering

end GroundZero.Types