import GroundZero.Support

open GroundZero.Proto (idfun Identity Identity.elem Identity.elim)
open GroundZero.Types.Id (ap apΩ)

universe u v w k
def AS {A : Type u} {B : Type v} {C : Type w} (x : A → B → C) (y : A → B) (z : A) := x z (y z)

section
  variable {A : Type u} {B : Type v}

  def Prod.Id {a c : A} {b d : B} (p : a = c) (q : b = d) : (a, b) = (c, d) :=
  begin induction p; induction q; reflexivity end

  def Prod.intro : A → B → A × B := Prod.mk
  def Prod.pr₁   : A × B → A     := Prod.fst
  def Prod.pr₂   : A × B → B     := Prod.snd
end

namespace GroundZero.Types
namespace Equiv

  def Homotopy {A : Type u} {B : A → Type v} (f g : Π x, B x) :=
  Π (x : A), f x = g x
  infix:80 " ~ " => Homotopy

  hott def Homotopy.id {A : Type u} {B : A → Type v} (f : Π x, B x) : f ~ f :=
  begin intro x; reflexivity end

  hott def Homotopy.symm {A : Type u} {B : A → Type v}
    (f g : Π (x : A), B x) (h : f ~ g) : g ~ f :=
  λ x, (h x)⁻¹

  hott def Homotopy.trans {A : Type u} {B : A → Type v}
    {f g h : Π (x : A), B x} (p : f ~ g) (q : g ~ h) : f ~ h :=
  λ x, p x ⬝ q x

  namespace Homotopy
    variable {A : Type u} {B : Type v} {C : Type w}

    hott def hcom {f₁ f₂ : B → C} {g₁ g₂ : A → B} (H : f₁ ~ f₂) (G : g₁ ~ g₂) : f₁ ∘ g₁ ~ f₂ ∘ g₂ :=
    λ x, H (g₁ x) ⬝ ap f₂ (G x)

    hott def rwhs {f : B → C} {g₁ g₂ : A → B} (H : g₁ ~ g₂) : f ∘ g₁ ~ f ∘ g₂ :=
    hcom (id f) H

    hott def lwhs {f₁ f₂ : B → C} {g : A → B} (H : f₁ ~ f₂) : f₁ ∘ g ~ f₂ ∘ g :=
    hcom H (id g)
  end Homotopy

  section
    variable {A : Type u} {B : A → Type v}
    instance : @Reflexive  (Π x, B x) (· ~ ·) := ⟨@Homotopy.id A B⟩
    instance : @Symmetric  (Π x, B x) (· ~ ·) := ⟨@Homotopy.symm A B⟩
    instance : @Transitive (Π x, B x) (· ~ ·) := ⟨@Homotopy.trans A B⟩
  end

  hott def Homotopy.Id {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (η : f = g) : f ~ g :=
  begin induction η; reflexivity end

  def linv {A : Type u} {B : Type v} (f : A → B) :=
  Σ (g : B → A), g ∘ f ~ idfun

  def rinv {A : Type u} {B : Type v} (f : A → B) :=
  Σ (g : B → A), f ∘ g ~ idfun

  def biinv {A : Type u} {B : Type v} (f : A → B) :=
  linv f × rinv f

  hott def homotopySquare {A : Type u} {B : Type v}
    {f g : A → B} (H : f ~ g) {x y : A} (p : x = y) :
    H x ⬝ ap g p = ap f p ⬝ H y :=
  begin induction p; transitivity; apply Id.reflRight; apply Id.reflLeft end
end Equiv

def Equiv (A : Type u) (B : Type v) : Type (max u v) :=
Σ (f : A → B), Equiv.biinv f
infix:25 " ≃ " => Equiv

namespace Equiv
  hott def forward {A : Type u} {B : Type v} (e : A ≃ B) : A → B := e.fst
  instance forwardCoe {A : Type u} {B : Type v} : CoeFun (A ≃ B) (λ _, A → B) := ⟨forward⟩

  hott def left {A : Type u} {B : Type v} (e : A ≃ B) : B → A := e.2.1.1
  hott def right {A : Type u} {B : Type v} (e : A ≃ B) : B → A := e.2.2.1

  hott def leftForward {A : Type u} {B : Type v} (e : A ≃ B) : e.left ∘ e.forward ~ id := e.2.1.2
  hott def forwardRight {A : Type u} {B : Type v} (e : A ≃ B) : e.forward ∘ e.right ~ id := e.2.2.2

  hott def ideqv (A : Type u) : A ≃ A :=
  ⟨idfun, (⟨idfun, idp⟩, ⟨idfun, idp⟩)⟩

  instance : @Reflexive (Type u) (· ≃ ·) := ⟨ideqv⟩

  hott def inveqv {A : Type u} {a b : A} : (a = b) ≃ (b = a) :=
  ⟨Id.inv, (⟨Id.inv, Id.invInv⟩, ⟨Id.inv, Id.invInv⟩)⟩

  hott def biinvTrans {A : Type u} {B : Type v} {C : Type w}
    {f : A → B} {g : B → C} (e₁ : biinv f) (e₂ : biinv g) : biinv (g ∘ f) :=
  (⟨e₁.1.1 ∘ e₂.1.1, λ x, ap e₁.1.1 (e₂.1.2 (f x)) ⬝ e₁.1.2 x⟩,
   ⟨e₁.2.1 ∘ e₂.2.1, λ x, ap g (e₁.2.2 (e₂.2.1 x)) ⬝ e₂.2.2 x⟩)

  hott def trans {A : Type u} {B : Type v} {C : Type w}
    (f : A ≃ B) (g : B ≃ C) : A ≃ C :=
  ⟨g.1 ∘ f.1, biinvTrans f.2 g.2⟩

  instance : @Transitive (Type u) (· ≃ ·) := ⟨@trans⟩

  hott def idtoeqv {A B : Type u} (p : A = B) : A ≃ B :=
  begin induction p; reflexivity end

  hott def idtoiff {A B : Type u} (p : A = B) : A ↔ B :=
  begin induction p; reflexivity end

  def transport {A : Type u} (B : A → Type v) {a b : A} (p : a = b) : B a → B b :=
  begin induction p; apply idfun end

  hott def subst {A : Type u} {B : A → Type v} {a b : A} (p : a = b) : B a → B b :=
  transport B p

  hott def substInv {A : Type u} {B : A → Type v} {a b : A} (p : a = b) : B b → B a :=
  subst p⁻¹

  hott def transportconst {A B : Type u} : A = B → A → B :=
  transport idfun

  def transportconstInv {A B : Type u} : A = B → B → A :=
  transportconst ∘ Id.symm

  hott def transportconstOverInv {A B : Type u} (p : A = B) :
    Π x, transportconst p⁻¹ x = transportconstInv p x :=
  begin intro x; reflexivity end

  hott def happlyEqv {A : Type u} {B : Type v} {f g : A ≃ B}
    (p : f = g) : f.forward ~ g.forward :=
  begin induction p; reflexivity end

  instance {A : Type u} : @Rewrite A A A Id Id Id := ⟨@Id.trans A⟩

  instance {A : Type u} {B : Type v} (ρ : A → B → Type w) : Rewrite ρ Id ρ :=
  ⟨λ a _ _ R p => transport (ρ a) p R⟩

  instance {A : Type u} {B : Type v} (ρ : A → B → Type w) : Rewrite Id ρ ρ :=
  ⟨λ _ _ c p R => transport (ρ · c) p⁻¹ R⟩

  instance : Rewrite Equiv.{u, v} Equiv.{v, w} Equiv.{u, w} := ⟨@trans⟩

  def depPath {A : Type u} (B : A → Type v) {a b : A} (p : a = b) (u : B a) (v : B b) :=
  Equiv.subst p u = v

  notation u " =[" P ", " p "] " v => depPath P p u v
  notation u " =[" p "] " v        => depPath _ p u v

  hott def depPath.refl {A : Type u} (B : A → Type v) {a : A} (u : B a) : u =[idp a] u :=
  idp u

  instance {A : Type u} (B : A → Type v) (a : A) :
    @Reflexive (B a) (depPath B (idp a)) :=
  ⟨depPath.refl B⟩

  hott def JTrans {A : Type} {a : A} (B : Π x, a = x → Type v)
    {b c : A} (p : a = b) (q : b = c) (w : B a (idp a)) :
      J₁ B w (p ⬝ q) = J₁ (λ x r, B x (p ⬝ r)) (subst (Id.reflRight _)⁻¹ (@Id.rec A a B w b p)) q :=
  begin induction p; induction q; reflexivity end

  hott def compInvCancelCoh {A : Type u} {a b : A} {B : a = b → Type v} (p : a = b) (w : B p) :
    subst (Id.cancelInvComp p p) (transport (λ r, B (r ⬝ p)) (Id.compInv p)⁻¹ w) = w :=
  begin induction p; reflexivity end

  hott def pathoverOfEq {A : Type u} {B : Type v} {a b : A} {a' b' : B}
    (p : a = b) (q : a' = b') : a' =[λ _, B, p] b' :=
  begin induction p; apply q end

  hott theorem transportForwardAndBack {A : Type u} {B : A → Type v}
    {x y : A} (p : x = y) (u : B x) : subst p⁻¹ (subst p u) = u :=
  begin induction p; reflexivity end

  hott theorem transportBackAndForward {A : Type u} {B : A → Type v}
    {x y : A} (p : x = y) (u : B y) : subst p (subst p⁻¹ u) = u :=
  begin induction p; reflexivity end

  hott theorem substComp {A : Type u} {B : A → Type v} {a b c : A}
    (p : a = b) (q : b = c) (x : B a) : subst (p ⬝ q) x = subst q (subst p x) :=
  begin induction p; induction q; reflexivity end

  hott def depSymm {A : Type u} {B : A → Type v} {a b : A}
    (p : a = b) {u : B a} {v : B b} (q : u =[p] v) : v =[p⁻¹] u :=
  begin induction p; exact q⁻¹ end

  hott def depTrans {A : Type u} {B : A → Type v}
    {a b c : A} {p : a = b} {q : b = c} {u : B a} {v : B b} {w : B c}
    (r : u =[p] v) (s : v =[q] w): u =[p ⬝ q] w :=
  begin induction r using Id.casesOn; induction s using Id.casesOn; apply substComp end
  infix:60 " ⬝′ " => depTrans

  hott def depPathTransSymm {A : Type u} {B : A → Type v} {a b c : A} {p : a = b} {q : c = b}
    {x : B a} {y : B c} (η : x =[p ⬝ q⁻¹] y) : x =[p] subst q y :=
  begin induction p; induction q; exact η end

  hott def depPathTransSymmCoh {A : Type u} {B : A → Type v} {a b c : A} {p : a = b} {q : c = b}
    {x : B a} {y : B c} : Π (η : x =[p ⬝ q⁻¹] y), depPathTransSymm η ⬝′ depSymm q (idp _) = η :=
  begin induction p; induction q; intro (η : x = y); induction η; apply idp end

  hott theorem substOverPathComp {A : Type u} {B : A → Type v} {a b c : A}
    (p : a = b) (q : b = c) (x : B a) : subst (p ⬝ q) x = subst q (subst p x) :=
  begin induction p; reflexivity end

  hott theorem substOverInvPath {A : Type u} {B : A → Type v} {a b : A}
    (p : a = b) (x : B b) : subst p⁻¹ x = substInv p x :=
  by reflexivity

  hott def apd {A : Type u} {B : A → Type v} {a b : A}
    (f : Π (x : A), B x) (p : a = b) : subst p (f a) = f b :=
  begin induction p; reflexivity end

  hott lemma apdInv {A : Type u} {B : A → Type v} {a b : A}
    (f : Π (x : A), B x) (p : a = b) : apd f p⁻¹ = depSymm p (apd f p) :=
  begin induction p; reflexivity end

  hott theorem apdFunctoriality {A : Type u} {B : A → Type v} {a b c : A}
    (f : Π x, B x) (p : a = b) (q : b = c) :
    @apd A B a c f (p ⬝ q) = apd f p ⬝′ apd f q :=
  begin induction p; induction q; reflexivity end

  hott def substSquare {A : Type u} {B : A → Type v} {a b : A}
    {p q : a = b} (r : p = q) (u : B a) : subst p u = subst q u :=
  begin induction r; reflexivity end

  notation "subst²" => substSquare

  hott def depPathMap {A : Type u} {B : A → Type v} {δ : A → Type w} {a b : A}
    {p : a = b} {u : B a} {v : B b} (g : Π x, B x → δ x) (q : u =[p] v) : g a u =[p] g b v :=
  begin induction p; induction q using Id.casesOn; reflexivity end

  hott def depPathMap' {A : Type u} {B : Type v} {C : A → Type w} {D : B → Type k}
    {a b : A} {p : a = b} {u : C a} {v : C b} (f : A → B)
    (g : Π x, C x → D (f x)) (q : u =[p] v) : g a u =[ap f p] g b v :=
  begin induction p; induction q using Id.casesOn; apply idp end

  def transportInv {A : Type u} (B : A → Type v) {a b : A} (p : a = b) : B b → B a :=
  substInv p

  def transportSquare {A : Type u} (B : A → Type v) {a b : A}
    {p q : a = b} (r : p = q) (u : B a) : subst p u = subst q u :=
  substSquare r u

  notation "transport²" => transportSquare

  hott theorem transportComp {A : Type u} {B : Type v}
    (C : B → Type w) {x y : A} (f : A → B) (p : x = y) (u : C (f x)) :
    transport (C ∘ f) p u = transport C (ap f p) u :=
  begin induction p; reflexivity end

  hott theorem transportToTransportconst {A : Type u} (B : A → Type v) {a b : A}
    (p : a = b) (u : B a) : transport B p u = transportconst (ap B p) u :=
  begin induction p; reflexivity end

  hott theorem transportconstOverComposition {A B C : Type u} (p : A = B) (q : B = C) (x : A) :
    transportconst (p ⬝ q) x = transportconst q (transportconst p x) :=
  by apply substOverPathComp

  hott theorem transportComposition {A : Type u} {a x₁ x₂ : A}
    (p : x₁ = x₂) (q : a = x₁) : transport (Id a) p q = q ⬝ p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott theorem transportCompositionRev {A : Type u} {a x₁ x₂ : A}
    (p : x₁ = x₂) (q : x₁ = a) : transport (· = a) p q = p⁻¹ ⬝ q :=
  begin induction p; reflexivity end

  hott theorem transportCharacterization {A : Type u} {B : A → Type v} {C : A → Type w} {a b : A}
    (φ : B a → C a) (p : a = b) : transport (λ x, B x → C x) p φ = transport C p ∘ φ ∘ transport B p⁻¹ :=
  begin induction p; reflexivity end

  hott theorem transportOverFamily {A : Type u} {x y : A} {B δ : A → Type v}
    (f : Π x, B x → δ x) (p : x = y) (u : B x) : subst p (f x u) = f y (subst p u) :=
  begin induction p; reflexivity end

  hott def biapd {A : Type u} {B : A → Type v} {C : A → Type w} {a b : A} {u : B a} {v : B b}
    (f : Π x, B x → C x) (p : a = b) (q : u =[p] v) : f a u =[p] f b v :=
  begin induction p; exact ap (f a) q end

  hott def apd₂ {A : Type u} {B : A → Type v} {a b : A} {p q : a = b}
    (f : Π x, B x) (r : p = q) : apd f p =[λ s, subst s (f a) = f b, r] apd f q :=
  begin induction r; reflexivity end

  hott lemma rewriteComp {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} (h : r = p ⬝ q) : p⁻¹ ⬝ r = q :=
  begin induction p; apply h end

  hott lemma invRewriteComp {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} (h : p⁻¹ ⬝ r = q) : r = p ⬝ q :=
  begin induction p; apply h end

  hott lemma invCompRewrite {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} (h : p ⬝ q = r) : p = r ⬝ q⁻¹ :=
  begin induction q; exact (Id.reflRight p)⁻¹ ⬝ h ⬝ (Id.reflRight r)⁻¹ end

  hott lemma cancelHigherConjLeft {A : Type u} {a b : A} {p : a = b} (ν κ : p = p) : κ⁻¹ ⬝ ν ⬝ κ = ν :=
  begin transitivity; symmetry; apply Id.assoc; apply rewriteComp; apply Whiskering.comm end

  hott lemma cancelHigherConjRight {A : Type u} {a b : A} {p : a = b} (ν κ : p = p) : κ ⬝ ν ⬝ κ⁻¹ = ν :=
  begin symmetry; apply invCompRewrite; apply Whiskering.comm end

  hott corollary cancelDoubleConjLeftLeft {A : Type u} {a b : A} {p q : a = b}
    (ν : p = p) (κ : p = q) (ε : q = p) : ε⁻¹ ⬝ (κ⁻¹ ⬝ ν ⬝ κ) ⬝ ε = ν :=
  begin induction ε; transitivity; apply Id.reflRight; apply cancelHigherConjLeft end

  hott corollary cancelDoubleConjRightRight {A : Type u} {a b : A} {p q : a = b}
    (ν : q = q) (κ : p = q) (ε : q = p) : ε ⬝ (κ ⬝ ν ⬝ κ⁻¹) ⬝ ε⁻¹ = ν :=
  begin induction ε; transitivity; apply Id.reflRight; apply cancelHigherConjRight end

  hott corollary cancelDoubleConjRightLeft {A : Type u} {a b : A} {p q : a = b}
    (ν : q = q) (κ : q = p) (ε : q = p) : ε ⬝ (κ⁻¹ ⬝ ν ⬝ κ) ⬝ ε⁻¹ = ν :=
  begin induction ε; transitivity; apply Id.reflRight; apply cancelHigherConjLeft end

  hott corollary cancelDoubleConjLeftRight {A : Type u} {a b : A} {p q : a = b}
    (ν : q = q) (κ : p = q) (ε : p = q) : ε⁻¹ ⬝ (κ ⬝ ν ⬝ κ⁻¹) ⬝ ε = ν :=
  begin induction ε; transitivity; apply Id.reflRight; apply cancelHigherConjRight end

  hott def idConjIfComm {A : Type u} {a b : A} (p : a = b) (q : a = a) (r : b = b) :
    p ⬝ r = q ⬝ p → q⁻¹ ⬝ p ⬝ r = p :=
  begin intro ε; transitivity; symmetry; apply Id.assoc; apply rewriteComp; exact ε end

  hott def idConjRevIfComm {A : Type u} {a b : A} (p : a = b) (q : a = a) (r : b = b) :
    p ⬝ r = q ⬝ p → q ⬝ p ⬝ r⁻¹ = p :=
  begin intro ε; symmetry; apply invCompRewrite; exact ε end

  hott lemma mapWithHomotopy {A : Type u} {B : Type v} (f g : A → B) (H : f ~ g) {a b : A} (p : a = b) :
    ap f p = H a ⬝ ap g p ⬝ (H b)⁻¹ :=
  begin apply invCompRewrite; symmetry; apply homotopySquare end

  hott def pathoverFromTrans {A : Type u} {a b c : A}
    (p : b = c) (q : a = b) (r : a = c) (η : q ⬝ p = r) : q =[p] r :=
  begin induction η; apply transportComposition end

  hott lemma transportInvCompComp {A : Type u} {a b : A} (p : a = b) (q : a = a) :
    Equiv.transport (λ x, x = x) p q = p⁻¹ ⬝ q ⬝ p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott theorem mapFunctoriality {A : Type u} {B : Type v}
    {a b c : A} (f : A → B) {p : a = b} {q : b = c} :
    ap f (p ⬝ q) = ap f p ⬝ ap f q :=
  begin induction p; reflexivity end

  hott corollary mapFunctoriality₃ {A : Type u} {B : Type v}
    {a b c d : A} (f : A → B) {p : a = b} {q : b = c} {r : c = d} :
    ap f (p ⬝ q ⬝ r) = ap f p ⬝ ap f q ⬝ ap f r :=
  begin induction p; induction q; reflexivity end

  hott corollary mapFunctoriality₄ {A : Type u} {B : Type v}
    {a b c d e : A} (f : A → B) {p : a = b} {q : b = c} {r : c = d} {s : d = e} :
    ap f (p ⬝ q ⬝ r ⬝ s) = ap f p ⬝ ap f q ⬝ ap f r ⬝ ap f s :=
  begin induction p; induction q; induction r; reflexivity end

  hott lemma transportOverContrMap {A : Type u} {B : Type v} {a b : A} {c : B}
    (f : A → B) (p : a = b) (q : f a = c) :
    transport (λ x, f x = c) p q = ap f p⁻¹ ⬝ q :=
  begin induction p; reflexivity end

  hott lemma transportOverInvContrMap {A : Type u} {B : Type v} {a b : A} {c : B}
    (f : A → B) (p : a = b) (q : c = f a) :
    transport (λ x, c = f x) p q = q ⬝ ap f p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott lemma transportOverInvolution {A : Type u} {a b : A} (f : A → A) (p : a = b) (q : f a = a) :
    transport (λ x, f x = x) p q = ap f p⁻¹ ⬝ q ⬝ p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott lemma transportOverHmtpy {A : Type u} {B : Type v} {a b : A} (f g : A → B) (p : a = b) (q : f a = g a) :
    transport (λ x, f x = g x) p q = ap f p⁻¹ ⬝ q ⬝ ap g p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott lemma idmap {A : Type u} {a b : A} (p : a = b) : ap idfun p = p :=
  begin induction p; reflexivity end

  hott lemma constmap {A : Type u} {B : Type v} {a b : A} {c : B}
    (p : a = b) : ap (λ _, c) p = idp c :=
  begin induction p; reflexivity end

  hott theorem transportOverDhmtpy {A : Type u} {B : A → Type v} {a b : A}
    (f g : Π x, B x) (p : a = b) (q : f a = g a) :
    transport (λ x, f x = g x) p q = (apd f p)⁻¹ ⬝ ap (subst p) q ⬝ apd g p :=
  begin induction p; symmetry; transitivity; apply Id.reflRight; apply idmap end

  hott theorem mapOverComp {A : Type u} {B : Type v} {C : Type w} {a b : A}
    (f : A → B) (g : B → C) (p : a = b) :
    @ap A C a b (g ∘ f) p = ap g (ap f p) :=
  begin induction p; reflexivity end

  section
    variable {A : Type u} {B : Type v} {C : B → Type w} (f : A → B) {a b : A} {u : C (f a)} {v : C (f b)} (p : a = b)

    hott def pathOverAp : (u =[C, ap f p] v) → (u =[C ∘ f, p] v) :=
    begin induction p; exact idfun end

    hott def pathUnderAp : (u =[C ∘ f, p] v) → (u =[C, ap f p] v) :=
    begin induction p; exact idfun end

    hott lemma pathOverApCoh : pathOverAp f p ∘ @pathUnderAp A B C f a b u v p ~ idfun :=
    begin intro; induction p; reflexivity end

    hott lemma pathUnderApCoh : pathUnderAp f p ∘ @pathOverAp A B C f a b u v p ~ idfun :=
    begin intro; induction p; reflexivity end
  end

  hott theorem apdOverComp {A : Type u} {B : Type v} {C : B → Type w} {a b : A} (f : Π x, C x) (g : A → B)
    (p : a = b) : apd (λ x, f (g x)) p = pathOverAp g p (apd f (ap g p)) :=
  begin induction p; reflexivity end

  hott theorem apdOverConstantFamily {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : a = b) : apd f p = pathoverOfEq p (ap f p) :=
  begin induction p; reflexivity end

  def reflPathover {A : Type u} {B : Type v} {a : A} {x y : B} (p : x =[λ _, B, idp a] y) : x = y := p

  hott lemma pathoverInv {A : Type u} {B : Type v} (a : A) {x y : B} (p : x = y) :
    reflPathover (pathoverOfEq (idp a) p) = p :=
  begin induction p; reflexivity end

  hott def pathoverOfEqInj {A : Type u} {B : Type v} {a b : A} {a' b' : B}
    (r : a = b) (p q : a' = b') (η : pathoverOfEq r p = pathoverOfEq r q) : p = q :=
  begin induction r; apply η end

  hott def transportImpl {A : Type u} (B : A → Type v)
    (C : A → Type w) {a b : A} (p : a = b) (φ : B a → C a) :
    transport (λ x, B x → C x) p φ = λ x, subst p (φ (subst p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott theorem transportOverConstFamily {A : Type u} {B : Type v}
    {a b : A} (p : a = b) (b : B) : transport (λ _, B) p b = b :=
  begin induction p; reflexivity end

  hott theorem transportOverPi {A : Type u} {B : Type v}
    (B : A → B → Type w) {a b : A} (p : a = b) (u : Π y, B a y) :
    transport (λ x, Π y, B x y) p u = (λ y, @transport A (λ x, B x y) a b p (u y)) :=
  begin induction p; reflexivity end

  hott theorem transportOverSig {A : Type u} {B : Type v}
    (B : A → B → Type w) {a b : A} (p : a = b) (u : Σ y, B a y) :
    transport (λ x, Σ y, B x y) p u = ⟨u.1, transport (B · u.1) p u.2⟩ :=
  begin induction p; reflexivity end

  hott theorem transportOverProduct {A : Type u} (F : A → Type v) (G : A → Type w) {a b : A}
    (p : a = b) {w : F a × G a} : transport (λ x, F x × G x) p w = (transport F p w.1, transport G p w.2) :=
  begin induction p; reflexivity end

  hott lemma transportOverFunction {A : Type u} {B : Type v}
    {a : A} {b : B} (f g : A → B) (p : f = g) (q : f a = b) :
    transport (λ (f' : A → B), f' a = b) p q =
    @ap (A → B) B g f (λ (f' : A → B), f' a) p⁻¹ ⬝ q :=
  begin induction p; reflexivity end

  hott lemma transportOverOperation {A B : Type u} (φ : A → A → A) (p : A = B) :
    transport (λ A, A → A → A) p φ = λ x y, transport idfun p (φ (transport idfun p⁻¹ x) (transport idfun p⁻¹ y)) :=
  begin induction p; reflexivity end

  hott lemma transportOverFunctor {A B : Type u} (M : Type u → Type v) (N : Type u → Type w)
    (φ : M A → N A) (p : A = B) : transport (λ A, M A → N A) p φ = λ x, subst p (φ (subst p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott lemma transportOverMorphism {A B : Type u} (φ : A → A) (p : A = B) :
    transport (λ A, A → A) p φ = λ x, transport idfun p (φ (transport idfun p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott lemma transportOverOperationPointwise {A B : Type u} (φ : A → A → A) (p : A = B) {x y : B} :
      transport (λ A, A → A → A) p φ x y
    = transport idfun p (φ (transport idfun p⁻¹ x) (transport idfun p⁻¹ y)) :=
  begin induction p; reflexivity end

  hott lemma transportOverMorphismPointwise {A B : Type u} (φ : A → A) (p : A = B) {x : B} :
    transport (λ A, A → A) p φ x = transport idfun p (φ (transport idfun p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott def bimap {A : Type u} {B : Type v} {C : Type w} {a b : A} {a' b' : B}
    (f : A → B → C) (p : a = b) (q : a' = b') : f a a' = f b b' :=
  begin induction p; induction q; reflexivity end

  hott lemma bimapReflLeft {A : Type u} {B : Type v} {C : Type w}
    {a : A} {a' b' : B} (f : A → B → C) (p : a' = b') :
    bimap f (idp a) p = ap (f a) p :=
  begin induction p; reflexivity end

  hott lemma bimapReflRight {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' : B} (f : A → B → C) (p : a = b) :
    bimap f p (idp a') = ap (f · a') p :=
  begin induction p; reflexivity end

  hott theorem bimapCharacterization {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' b' : B} (f : A → B → C) (p : a = b) (q : a' = b') :
    bimap f p q = @ap A C a b (f · a') p ⬝ ap (f b) q :=
  begin induction p; induction q; reflexivity end

  hott theorem bimapCharacterization' {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' b' : B} (f : A → B → C) (p : a = b) (q : a' = b') :
    bimap f p q = ap (f a) q ⬝ @ap A C a b (f · b') p :=
  begin induction p; induction q; reflexivity end

  hott theorem bimapInv {A : Type u} {B : Type v} {C : Type w} {a b : A} {a' b' : B}
    (f : A → B → C) (p : a = b) (q : a' = b') : (bimap f p q)⁻¹ = bimap f p⁻¹ q⁻¹ :=
  begin induction p; induction q; reflexivity end

  hott theorem bimapComp {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' b' : B} (f : A → B → C) (p : a = b) (q : a' = b') :
    ap (f · a') p = ap (f a) q ⬝ bimap f p q⁻¹ :=
  begin
    induction p; symmetry; transitivity; apply ap; transitivity;
    apply bimapReflLeft; apply Id.mapInv; apply Id.compInv
  end

  hott lemma transportBimap₁ {A : Type u} {B : Type v} {a₁ a₂ : A} {b₁ b₂ : B}
    (f : A → B → Type w) (p : a₁ = a₂) (q : b₁ = b₂) (u : f a₁ b₁) :
    transportconst (bimap f p q) u = transport (f · b₂) p (transport (f a₁) q u) :=
  begin induction p; induction q; reflexivity end

  hott lemma transportBimap₂ {A : Type u} {B : Type v} {a₁ a₂ : A} {b₁ b₂ : B}
    (f : A → B → Type w) (p : a₁ = a₂) (q : b₁ = b₂) (u : f a₁ b₁) :
    transportconst (bimap f p q) u = transport (f a₂) q (transport (f · b₁) p u) :=
  begin induction p; induction q; reflexivity end

  hott def transportDiag₁ {A : Type u} (B : A → A → Type v) {a b : A} {p : a = b} (w : B a a) :
    transport (λ x, B x x) p w = transport (B b) p (transport (B · a) p w) :=
  begin induction p; reflexivity end

  hott def transportDiag₂ {A : Type u} (B : A → A → Type v) {a b : A} {p : a = b} (w : B a a) :
    transport (λ x, B x x) p w = transport (B · b) p (transport (B a) p w) :=
  begin induction p; reflexivity end

  hott def bimapBicom {A : Type u} {B : Type v} {C : Type w} {D : Type k}
    (f : D → A) (g : D → B) (h : A → B → C) {x y : D} (p : x = y) :
    ap (λ x, h (f x) (g x)) p = bimap h (ap f p) (ap g p) :=
  begin induction p; reflexivity end

  hott theorem mapOverAS {A : Type u} {a b : A} (f : A → A → A) (g : A → A) (p : a = b) :
    ap (AS f g) p = @bimap A A A a b (g a) (g b) f p (ap g p) :=
  begin induction p; reflexivity end

  hott lemma liftedHapply {A : Type u} (B : A → Type v) (C : A → Type w)
    {a b : A} (p : a = b) (f : B a → C a) (g : B b → C b)
    (q : transport (λ x, B x → C x) p f = g) :
    Π x, transport C p (f x) = g (transport B p x) :=
  begin induction p; induction q; intro x; reflexivity end

  hott statement identityEqv {A : Type u} : A ≃ Identity A :=
  begin
    existsi Identity.elem; apply Prod.mk <;> existsi Identity.elim <;> intro x;
    { reflexivity }; { induction x; reflexivity }
  end

  hott def eqvEqEqv {A B C : Type u} (p : A ≃ B) (q : B = C) : A ≃ C :=
  transport (Equiv A) q p

  hott corollary apComHmtpy {A : Type u} {B : Type v} {f g : A → B}
    (H : f ~ g) {a b : A} (p : a = b) : (f a = f b) = (g a = g b) :=
  bimap Id (H a) (H b)

  hott lemma apdComHmtpy {A : Type u} {B : A → Type v} {f g : Π x, B x} (H : f ~ g)
    {a b : A} (p : a = b) : (f a =[B, p] f b) = (g a =[B, p] g b) :=
  bimap Id (ap (transport B p) (H a)) (H b)

  hott def conjugateOver {A : Type u} {B : A → Type v} {C : A → Type w}
    {φ ψ : Π x, B x → C x} (H : Π x, φ x ~ ψ x) {a b : A} {u : B a} {v : B b}
    {p : a = b} (q : φ a u =[C, p] φ b v) : ψ a u =[C, p] ψ b v :=
  begin induction p; exact (H a u)⁻¹ ⬝ q ⬝ H a v end

  hott lemma biapdWithHomotopy {A : Type u} {B₁ : A → Type v} {B₂ : A → Type w}
    {φ ψ : Π x, B₁ x → B₂ x} (H : Π x, φ x ~ ψ x) {a b : A} {u : B₁ a} {v : B₁ b}
    (p : a = b) (q : u =[B₁, p] v) : biapd φ p q = conjugateOver (λ x y, (H x y)⁻¹) (biapd ψ p q) :=
  begin
    induction p; induction q using J₁; symmetry; transitivity;
    apply ap (· ⬝ _); apply Id.reflRight; apply Id.invComp
  end

  hott lemma biapdIdfun {A : Type u} {B : A → Type v} {a b : A}
    {u : B a} {v : B b} {p : a = b} (q : u =[B, p] v) : biapd (λ _, idfun) p q = q :=
  begin induction p; apply idmap end

  hott lemma comBiapd {A : Type u} {B₁ : A → Type v} {B₂ : A → Type w} {B₃ : A → Type k}
    (ψ : Π x, B₂ x → B₃ x) (φ : Π x, B₁ x → B₂ x) {a b : A} {u : B₁ a} {v : B₁ b}
    (p : a = b) (q : u =[B₁, p] v) : biapd (λ x, ψ x ∘ φ x) p q = biapd ψ p (biapd φ p q) :=
  begin induction p; apply mapOverComp end

  hott def bimapΩ {A : Type u} {B : Type v} {C : Type w} (f : A → B → C) {a : A} {b : B} :
    Π {n : ℕ}, Ωⁿ(A, a) → Ωⁿ(B, b) → Ωⁿ(C, f a b)
  | Nat.zero   => f
  | Nat.succ _ => bimapΩ (bimap f)

  hott def conjugateΩ {A : Type u} {a b : A} (p : a = b) {n : ℕ} : Ωⁿ(A, a) → Ωⁿ(A, b) :=
  transport (λ x, Ωⁿ(A, x)) p

  instance {A : Type u} {a b : A} {n : ℕ} : HPow (Ωⁿ(A, a)) (a = b) (Ωⁿ(A, b)) :=
  ⟨λ p α, conjugateΩ α p⟩

  hott lemma conjugateRewriteΩ {A : Type u} {a b : A} (p : a = b) {n : ℕ}
    (α : Ωⁿ(A, a)) (β : Ωⁿ(A, b)) : α = β^p⁻¹ → α^p = β :=
  begin induction p; apply idfun end

  hott lemma conjugateRewriteInvΩ {A : Type u} {a b : A} (p : a = b) {n : ℕ}
    (α : Ωⁿ(A, a)) (β : Ωⁿ(A, b)) : α^p = β → α = β^p⁻¹ :=
  begin induction p; apply idfun end

  hott theorem apConjugateΩ {A : Type u} {B : Type v} (f : A → B) {a b : A} (p : a = b)
    (n : ℕ) (α : Ωⁿ(A, a)) : apΩ f (α^p) = (apΩ f α)^(ap f p) :=
  begin induction p; reflexivity end

  hott theorem conjugateTransΩ {A : Type u} {a b c : A} (p : a = b) (q : b = c)
    (n : ℕ) (α : Ωⁿ(A, a)) : α^(p ⬝ q) = (α^p)^q :=
  begin induction p; reflexivity end

  hott lemma conjugateRevRightΩ {A : Type u} {a b : A} (p : a = b)
    (n : ℕ) (α : Ωⁿ(A, a)) : (α^p)^p⁻¹ = α :=
  begin induction p; reflexivity end

  hott lemma conjugateRevLeftΩ {A : Type u} {a b : A} (p : a = b)
    (n : ℕ) (α : Ωⁿ(A, b)) : (α^p⁻¹)^p = α :=
  begin induction p; reflexivity end

  hott def LoopOver {A : Type u} (B : A → Type v) {a : A} (b : B a) : Π (n : ℕ), Ωⁿ(A, a) → Type v
  | Nat.zero,   x => B x
  | Nat.succ n, α => @LoopOver (a = a) (λ p, b =[p] b) (idp a) (idp b) n α

  macro:max "Ω" n:superscript "(" τ:term ", " ε:term ", " η:term ")" : term => do
    `(@LoopOver _ $τ _ $ε $(← Meta.Notation.parseSuperscript n) $η)

  macro:max "Ω" "[" n:term "]" "(" τ:term ", " ε:term ", " η:term ")" : term => do
    `(@LoopOver _ $τ _ $ε $n $η)

  @[app_unexpander LoopOver]
  def loopOverUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $B $b $n $α) => `(Ω[$n]($B, $b, $α))
  | _                 => throw ()

  hott def apdΩ {A : Type u} {B : A → Type v} (f : Π x, B x)
    {a : A} : Π {n : ℕ} (α : Ωⁿ(A, a)), Ωⁿ(B, f a, α)
  | Nat.zero   => f
  | Nat.succ _ => apdΩ (apd f)

  hott def conjugateOverΩ {A : Type u} {B : A → Type v} {a : A} {b₁ b₂ : B a}
    {n : ℕ} {α : Ωⁿ(A, a)} (p : b₁ = b₂) : Ωⁿ(B, b₁, α) → Ωⁿ(B, b₂, α) :=
  transport (λ x, Ωⁿ(B, x, α)) p

  hott def biapdΩ {A : Type u} {B₁ : A → Type v} {B₂ : A → Type w} (φ : Π x, B₁ x → B₂ x) {a : A} {b : B₁ a} :
    Π (n : ℕ) (α : Ωⁿ(A, a)), Ωⁿ(B₁, b, α) → Ωⁿ(B₂, φ a b, α)
  | Nat.zero,   x => φ x
  | Nat.succ n, α => @biapdΩ (a = a) (λ p, b =[p] b) (λ p, φ a b =[p] φ a b) (biapd φ) (idp a) (idp b) n α

  hott def overApΩ {A : Type u} {B : Type v} (C : B → Type w) (f : A → B) {a : A} {b : C (f a)} :
    Π (n : ℕ) (α : Ωⁿ(A, a)) (β : Ωⁿ(C, b, apΩ f α)), Ωⁿ(C ∘ f, b, α)
  | Nat.zero,   x, y => y
  | Nat.succ n, α, β => @biapdΩ (a = a) (λ p, b =[C, ap f p] b) (λ p, b =[C ∘ f, p] b)
                          (pathOverAp f) (idp a) (idp b) n α
                            (@overApΩ (a = a) (f a = f a) (λ p, b =[C, p] b) (ap f) (idp a) (idp b) n α β)

  hott def underApΩ {A : Type u} {B : Type v} (C : B → Type w) (f : A → B) {a : A} {b : C (f a)} :
    Π (n : ℕ) (α : Ωⁿ(A, a)) (β : Ωⁿ(C ∘ f, b, α)), Ωⁿ(C, b, apΩ f α)
  | Nat.zero,   x, y => y
  | Nat.succ n, α, β => @underApΩ (a = a) (f a = f a) (λ p, b =[C, p] b) (ap f) (idp a) (idp b) n α
                          (@biapdΩ (a = a) (λ p, b =[C ∘ f, p] b) (λ p, b =[C, ap f p] b)
                            (pathUnderAp f) (idp a) (idp b) n α β)

  hott def fillΩ {A : Type u} {B : A → Type v} {a b : A} {u : B a} {n : ℕ}
    {α : Ωⁿ(A, a)} (p : a = b) : Ωⁿ(B, u, α) → Ωⁿ(B, transport B p u, α^p) :=
  begin induction p; fapply idfun end

  hott def fillHaeΩ {A : Type u} {B : A → Type v} {a b : A} {u : B a} {n : ℕ}
    {α : Ωⁿ(A, a)} (p : a = b) : Ωⁿ(B, transport B p u, α^p) → Ωⁿ(B, u, α) :=
  begin induction p; fapply idfun end

  hott def fillConjugateΩ {A : Type u} {B : A → Type v} {a b : A} {u : B b} {n : ℕ}
    {α : Ωⁿ(A, a)} (p : a = b) : Ωⁿ(B, u, α^p) → Ωⁿ(B, transport B p⁻¹ u, α) :=
  λ β, fillHaeΩ p (conjugateOverΩ (transportBackAndForward p u)⁻¹ β)

  hott def apdConjugateΩ {A : Type u} {B : A → Type v} (f : Π x, B x) {a b : A} (p : a = b) {n : ℕ}
    (α : Ωⁿ(A, a)) : apdΩ f (α^p) = conjugateOverΩ (apd f p) (fillΩ p (apdΩ f α)) :=
  begin induction p; reflexivity end
end Equiv

def isQinv {A : Type u} {B : Type v} (f : A → B) (g : B → A) :=
(f ∘ g ~ idfun) × (g ∘ f ~ idfun)

def qinv {A : Type u} {B : Type v} (f : A → B) :=
Σ (g : B → A), isQinv f g

namespace Qinv
  open Equiv (biinv)
  open Id (ap)

  hott def linvInv {A : Type u} {B : Type v}
    (f : A → B) (g : B → A) (h : B → A)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : g ∘ f ~ id :=
  let F₁ := λ x, H (g (f x));
  let F₂ := λ x, ap h (G (f x));
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ H x

  hott def rinvInv {A : Type u} {B : Type v}
    (f : A → B) (g : B → A) (h : B → A)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : f ∘ h ~ id :=
  let F₁ := λ x, ap (f ∘ h) (G x);
  let F₂ := λ x, ap f (H (g x));
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ G x

  hott def toBiinv {A : Type u} {B : Type v} (f : A → B) (q : qinv f) : biinv f :=
  (⟨q.1, q.2.2⟩, ⟨q.1, q.2.1⟩)

  hott def ofBiinv {A : Type u} {B : Type v} (f : A → B) (F : biinv f) : qinv f :=
  ⟨F.2.1, (F.2.2, linvInv f F.2.1 F.1.1 F.2.2 F.1.2)⟩

  hott def ideqv {A : Type u} : qinv (@idfun A) :=
  ⟨idfun, (idp, idp)⟩

  hott def sym {A : Type u} {B : Type v} {f : A → B} (e : qinv f) : qinv e.1 :=
  ⟨f, (e.2.2, e.2.1)⟩

  hott def com {A : Type u} {B : Type v} {C : Type w} {g : B → C} {f : A → B} :
    qinv g → qinv f → qinv (g ∘ f) :=
  λ e₁ e₂, ⟨e₂.1 ∘ e₁.1, (λ c, ap g (e₂.2.1 (e₁.1 c)) ⬝ e₁.2.1 c,
                          λ a, ap e₂.1 (e₁.2.2 (f a)) ⬝ e₂.2.2 a)⟩

  hott def toEquiv {A : Type u} {B : Type v} {f : A → B} (e : qinv f) : A ≃ B :=
  ⟨f, (⟨e.1, e.2.2⟩, ⟨e.1, e.2.1⟩)⟩
end Qinv

namespace Equiv
  hott def forwardLeft {A : Type u} {B : Type v} (e : A ≃ B) : e.forward ∘ e.left ~ idfun :=
  begin apply Qinv.rinvInv; apply e.forwardRight; apply e.leftForward end

  hott def rightForward {A : Type u} {B : Type v} (e : A ≃ B) : e.right ∘ e.forward ~ idfun :=
  begin apply Qinv.linvInv; apply e.forwardRight; apply e.leftForward end

  hott def symm {A : Type u} {B : Type v} (f : A ≃ B) : B ≃ A :=
  Qinv.toEquiv (Qinv.sym (Qinv.ofBiinv f.1 f.2))

  instance : @Symmetric (Type u) (· ≃ ·) := ⟨@Equiv.symm⟩

  hott lemma eqvInj {A : Type u} {B : Type v} (e : A ≃ B)
    (x y : A) (p : e.forward x = e.forward y) : x = y :=
  begin
    transitivity; symmetry; apply e.leftForward;
    transitivity; apply ap e.left;
    exact p; apply e.leftForward
  end

  hott lemma eqvLeftInj {A : Type u} {B : Type v} (e : A ≃ B)
    (x y : B) (p : e.left x = e.left y) : x = y :=
  begin
    transitivity; symmetry; apply e.forwardLeft;
    transitivity; apply ap e.forward;
    exact p; apply e.forwardLeft
  end

  hott lemma eqvRightInj {A : Type u} {B : Type v} (e : A ≃ B)
    (x y : B) (p : e.right x = e.right y) : x = y :=
  begin
    transitivity; symmetry; apply e.forwardRight;
    transitivity; apply ap e.forward;
    exact p; apply e.forwardRight
  end
end Equiv

-- half adjoint equivalence
def ishae {A : Type u} {B : Type v} (f : A → B) :=
Σ (g : B → A) (η : g ∘ f ~ id) (ϵ : f ∘ g ~ id), Π x, ap f (η x) = ϵ (f x)

def fib {A : Type u} {B : Type v} (f : A → B) (y : B) := Σ (x : A), f x = y
def total {A : Type u} (B : A → Type v) := Σ x, B x
def fiberwise {A : Type u} (B : A → Type v) := Π x, B x

end GroundZero.Types
