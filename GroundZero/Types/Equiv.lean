import GroundZero.Support
open GroundZero.Proto (idfun Identity Identity.elem Identity.elim)

def AS (x : A → B → C) (y : A → B) (z : A) := x z (y z)

section
  universe u v
  variable {A : Type u} {B : Type v}

  def Prod.Id {a c : A} {b d : B} (p : a = c) (q : b = d) : (a, b) = (c, d) :=
  begin induction p; induction q; reflexivity end

  def Prod.intro : A → B → A × B := Prod.mk
  def Prod.pr₁   : A × B → A     := Prod.fst
  def Prod.pr₂   : A × B → B     := Prod.snd
end

namespace GroundZero.Types
universe u v w k

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
    H x ⬝ Id.map g p = Id.map f p ⬝ H y :=
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
  (⟨e₁.1.1 ∘ e₂.1.1, λ x, Id.map e₁.1.1 (e₂.1.2 (f x)) ⬝ e₁.1.2 x⟩,
   ⟨e₁.2.1 ∘ e₂.2.1, λ x, Id.map g (e₁.2.2 (e₂.2.1 x)) ⬝ e₂.2.2 x⟩)

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
  notation u " =[" p "] " v       => depPath _ p u v

  hott def depPath.refl {A : Type u} (B : A → Type v) {a : A} (u : B a) : u =[idp a] u :=
  idp u

  instance {A : Type u} (B : A → Type v) (a : A) :
    @Reflexive (B a) (depPath B (idp a)) :=
  ⟨depPath.refl B⟩

  hott def pathoverOfEq {A : Type u} {B : Type v} {a b : A} {a' b' : B}
    (p : a = b) (q : a' = b') : a' =[λ _, B, p] b' :=
  begin induction p; apply q end

  hott def transportForwardAndBack {A : Type u} {B : A → Type v}
    {x y : A} (p : x = y) (u : B x) : subst p⁻¹ (subst p u) = u :=
  begin induction p; reflexivity end

  hott def transportBackAndForward {A : Type u} {B : A → Type v}
    {x y : A} (p : x = y) (u : B y) : subst p (subst p⁻¹ u) = u :=
  begin induction p; reflexivity end

  hott def substComp {A : Type u} {B : A → Type v} {a b c : A}
    (p : a = b) (q : b = c) (x : B a) : subst (p ⬝ q) x = subst q (subst p x) :=
  begin induction p; induction q; reflexivity end

  hott def depSymm {A : Type u} {B : A → Type v} {a b : A}
    (p : a = b) {u : B a} {v : B b} (q : u =[p] v) : v =[p⁻¹] u :=
  begin induction q using Id.casesOn; apply transportForwardAndBack end

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

  hott def substOverPathComp {A : Type u} {B : A → Type v} {a b c : A}
    (p : a = b) (q : b = c) (x : B a) : subst (p ⬝ q) x = subst q (subst p x) :=
  begin induction p; reflexivity end

  hott def substOverInvPath {A : Type u} {B : A → Type v} {a b : A}
    (p : a = b) (x : B b) : subst p⁻¹ x = substInv p x :=
  by reflexivity

  hott def apd {A : Type u} {B : A → Type v} {a b : A}
    (f : Π (x : A), B x) (p : a = b) : subst p (f a) = f b :=
  begin induction p; reflexivity end

  hott def apdInv {A : Type u} {B : A → Type v} {a b : A}
    (f : Π (x : A), B x) (p : a = b) : apd f p⁻¹ = depSymm p (apd f p) :=
  begin induction p; reflexivity end

  hott def apdFunctoriality {A : Type u} {B : A → Type v} {a b c : A}
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
    (g : Π x, C x → D (f x)) (q : u =[p] v) : g a u =[Id.map f p] g b v :=
  begin induction p; induction q using Id.casesOn; apply idp end

  def transportInv {A : Type u} (B : A → Type v) {a b : A} (p : a = b) : B b → B a :=
  substInv p

  def transportSquare {A : Type u} (B : A → Type v) {a b : A}
    {p q : a = b} (r : p = q) (u : B a) : subst p u = subst q u :=
  substSquare r u

  notation "transport²" => transportSquare

  hott def transportComp {A : Type u} {B : Type v}
    (C : B → Type w) {x y : A} (f : A → B) (p : x = y) (u : C (f x)) :
    transport (C ∘ f) p u = transport C (Id.map f p) u :=
  begin induction p; reflexivity end

  hott def transportToTransportconst {A : Type u} (B : A → Type v) {a b : A}
    (p : a = b) (u : B a) : Equiv.transport B p u = Equiv.transportconst (Id.map B p) u :=
  begin induction p; reflexivity end

  hott def transportconstOverComposition {A B C : Type u} (p : A = B) (q : B = C)
    (x : A) : transportconst (p ⬝ q) x = transportconst q (transportconst p x) :=
  by apply substOverPathComp

  hott def transportComposition {A : Type u} {a x₁ x₂ : A}
    (p : x₁ = x₂) (q : a = x₁) : transport (Id a) p q = q ⬝ p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott def transportCharacterization {A : Type u} {B C : A → Type v} {a b : A} (φ : B a → C a)
    (p : a = b) : transport (λ x, B x → C x) p φ = transport C p ∘ φ ∘ transport B p⁻¹ :=
  begin induction p; reflexivity end

  hott def transportOverFamily {A : Type u} {x y : A} {B δ : A → Type v}
    (f : Π x, B x → δ x) (p : x = y) (u : B x) : subst p (f x u) = f y (subst p u) :=
  begin induction p; reflexivity end

  hott def apdSqr {A : Type u} {B C : A → Type v} {a b : A} {u : B a} {v : B b} {p : a = b}
    (f : Π {x : A}, B x → C x) (q : u =[p] v) : f u =[p] f v :=
  begin induction p; induction q using Id.casesOn; reflexivity end

  hott def apd₂ {A : Type u} {B : A → Type v} {a b : A} {p q : a = b}
    (f : Π x, B x) (r : p = q) : apd f p =[λ s, subst s (f a) = f b, r] apd f q :=
  begin induction r; reflexivity end

  hott def rewriteComp {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} (h : r = p ⬝ q) : p⁻¹ ⬝ r = q :=
  begin induction p; apply h end

  hott def invRewriteComp {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} (h : p⁻¹ ⬝ r = q) : r = p ⬝ q :=
  begin induction p; apply h end

  hott def invCompRewrite {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} (h : p ⬝ q = r) : p = r ⬝ q⁻¹ :=
  begin induction q; exact (Id.reflRight p)⁻¹ ⬝ h ⬝ (Id.reflRight r)⁻¹ end

  hott def mapWithHomotopy {A : Type u} {B : Type v} (f g : A → B) (H : f ~ g) {a b : A} (p : a = b) :
    Id.map f p = H a ⬝ Id.map g p ⬝ (H b)⁻¹ :=
  begin apply invCompRewrite; symmetry; apply homotopySquare end

  hott def pathoverFromTrans {A : Type u} {a b c : A}
    (p : b = c) (q : a = b) (r : a = c) (η : q ⬝ p = r) : q =[p] r :=
  begin induction η; apply transportComposition end

  hott def transportInvCompComp {A : Type u} {a b : A} (p : a = b) (q : a = a) :
    Equiv.transport (λ x, x = x) p q = p⁻¹ ⬝ q ⬝ p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott def mapFunctoriality {A : Type u} {B : Type v}
    {a b c : A} (f : A → B) {p : a = b} {q : b = c} :
    Id.map f (p ⬝ q) = Id.map f p ⬝ Id.map f q :=
  begin induction p; reflexivity end

  hott def transportOverContrMap {A : Type u} {B : Type v} {a b : A} {c : B}
    (f : A → B) (p : a = b) (q : f a = c) :
    Equiv.transport (λ x, f x = c) p q = Id.map f p⁻¹ ⬝ q :=
  begin induction p; reflexivity end

  hott def transportOverInvContrMap {A : Type u} {B : Type v} {a b : A} {c : B}
    (f : A → B) (p : a = b) (q : c = f a) :
    Equiv.transport (λ x, c = f x) p q = q ⬝ Id.map f p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott def transportOverInvolution {A : Type u} {a b : A} (f : A → A) (p : a = b) (q : f a = a) :
    Equiv.transport (λ x, f x = x) p q = Id.map f p⁻¹ ⬝ q ⬝ p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott def transportOverHmtpy {A : Type u} {B : Type v} {a b : A} (f g : A → B) (p : a = b) (q : f a = g a) :
    Equiv.transport (λ x, f x = g x) p q = Id.map f p⁻¹ ⬝ q ⬝ Id.map g p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott def idmap {A : Type u} {a b : A} (p : a = b) : Id.map idfun p = p :=
  begin induction p; reflexivity end

  hott def constmap {A : Type u} {B : Type v} {a b : A} {c : B}
    (p : a = b) : Id.map (λ _, c) p = idp c :=
  begin induction p; reflexivity end

  hott def transportOverDhmtpy {A : Type u} {B : A → Type v} {a b : A}
    (f g : Π x, B x) (p : a = b) (q : f a = g a) :
    Equiv.transport (λ x, f x = g x) p q = (apd f p)⁻¹ ⬝ Id.map (subst p) q ⬝ apd g p :=
  begin induction p; symmetry; transitivity; apply Id.reflRight; apply idmap end

  hott def mapOverComp {A : Type u} {B : Type v} {C : Type w} {a b : A}
    (f : A → B) (g : B → C) (p : a = b) :
    @Id.map A C a b (g ∘ f) p = Id.map g (Id.map f p) :=
  begin induction p; reflexivity end

  hott def apdOverConstantFamily {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : a = b) : apd f p = pathoverOfEq p (Id.map f p) :=
  begin induction p; reflexivity end

  def reflPathover {A : Type u} {B : Type v} {a : A} {x y : B} (p : x =[λ _, B, idp a] y) : x = y := p

  hott def pathoverInv {A : Type u} {B : Type v} (a : A) {x y : B} (p : x = y) :
    reflPathover (pathoverOfEq (idp a) p) = p :=
  begin induction p; reflexivity end

  hott def pathoverOfEqInj {A : Type u} {B : Type v} {a b : A} {a' b' : B}
    (r : a = b) (p q : a' = b') (η : pathoverOfEq r p = pathoverOfEq r q) : p = q :=
  begin induction r; apply η end

  hott def transportImpl {A : Type u} (B : A → Type v)
    (C : A → Type w) {a b : A} (p : a = b) (φ : B a → C a) :
    transport (λ x, B x → C x) p φ = λ x, subst p (φ (subst p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott def transportOverConstFamily {A : Type u} {B : Type v}
    {a b : A} (p : a = b) (b : B) : transport (λ _, B) p b = b :=
  begin induction p; reflexivity end

  hott def transportOverPi {A : Type u} {B : Type v}
    (B : A → B → Type w) {a b : A} (p : a = b) (u : Π y, B a y) :
    transport (λ x, Π y, B x y) p u = (λ y, @transport A (λ x, B x y) a b p (u y)) :=
  begin induction p; reflexivity end

  hott def transportOverSig {A : Type u} {B : Type v}
    (B : A → B → Type w) {a b : A} (p : a = b) (u : Σ y, B a y) :
    transport (λ x, Σ y, B x y) p u = ⟨u.1, transport (B · u.1) p u.2⟩ :=
  begin induction p; reflexivity end

  hott def transportOverFunction {A : Type u} {B : Type v}
    {a : A} {b : B} (f g : A → B) (p : f = g) (q : f a = b) :
    transport (λ (f' : A → B), f' a = b) p q =
    @Id.map (A → B) B g f (λ (f' : A → B), f' a) p⁻¹ ⬝ q :=
  begin induction p; reflexivity end

  hott def transportOverOperation {A B : Type u} (φ : A → A → A) (p : A = B) :
    transport (λ A, A → A → A) p φ = λ x y, transport idfun p (φ (transport idfun p⁻¹ x) (transport idfun p⁻¹ y)) :=
  begin induction p; reflexivity end

  hott def transportOverFunctor {A B : Type u} (M : Type u → Type v) (N : Type u → Type w)
    (φ : M A → N A) (p : A = B) : transport (λ A, M A → N A) p φ = λ x, subst p (φ (subst p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott def transportOverMorphism {A B : Type u} (φ : A → A) (p : A = B) :
    transport (λ A, A → A) p φ = λ x, transport idfun p (φ (transport idfun p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott def transportOverOperationPointwise {A B : Type u} (φ : A → A → A) (p : A = B) {x y : B} :
      transport (λ A, A → A → A) p φ x y
    = transport idfun p (φ (transport idfun p⁻¹ x) (transport idfun p⁻¹ y)) :=
  begin induction p; reflexivity end

  hott def transportOverMorphismPointwise {A B : Type u} (φ : A → A) (p : A = B) {x : B} :
    transport (λ A, A → A) p φ x = transport idfun p (φ (transport idfun p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott def bimap {A : Type u} {B : Type v} {C : Type w} {a b : A} {a' b' : B}
    (f : A → B → C) (p : a = b) (q : a' = b') : f a a' = f b b' :=
  begin induction p; induction q; reflexivity end

  hott def bimapReflLeft {A : Type u} {B : Type v} {C : Type w}
    {a : A} {a' b' : B} (f : A → B → C) (p : a' = b') :
    bimap f (idp a) p = Id.map (f a) p :=
  begin induction p; reflexivity end

  hott def bimapReflRight {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' : B} (f : A → B → C) (p : a = b) :
    bimap f p (idp a') = Id.map (f · a') p :=
  begin induction p; reflexivity end

  hott def bimapCharacterization {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' b' : B} (f : A → B → C) (p : a = b) (q : a' = b') :
    bimap f p q = @Id.map A C a b (f · a') p ⬝ Id.map (f b) q :=
  begin induction p; induction q; reflexivity end

  hott def bimapCharacterization' {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' b' : B} (f : A → B → C) (p : a = b) (q : a' = b') :
    bimap f p q = Id.map (f a) q ⬝ @Id.map A C a b (f · b') p :=
  begin induction p; induction q; reflexivity end

  hott def bimapInv {A : Type u} {B : Type v} {C : Type w} {a b : A} {a' b' : B}
    (f : A → B → C) (p : a = b) (q : a' = b') : (bimap f p q)⁻¹ = bimap f p⁻¹ q⁻¹ :=
  begin induction p; induction q; reflexivity end

  hott def bimapComp {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' b' : B} (f : A → B → C) (p : a = b) (q : a' = b') :
    Id.map (f · a') p = Id.map (f a) q ⬝ bimap f p q⁻¹ :=
  begin
    induction p; symmetry; transitivity; apply Id.map; transitivity;
    apply bimapReflLeft; apply Id.mapInv; apply Id.compInv
  end

  hott def mapOverAS {A : Type u} {a b : A} (f : A → A → A) (g : A → A) (p : a = b) :
    Id.map (AS f g) p = @bimap A A A a b (g a) (g b) f p (Id.map g p) :=
  begin induction p; reflexivity end

  hott def liftedHapply {A : Type u} (B : A → Type v) (C : A → Type w)
    {a b : A} (p : a = b) (f : B a → C a) (g : B b → C b)
    (q : transport (λ x, B x → C x) p f = g) :
    Π x, transport C p (f x) = g (transport B p x) :=
  begin induction p; induction q; intro x; reflexivity end

  hott def identityEqv {A : Type u} : A ≃ Identity A :=
  begin
    existsi Identity.elem; apply Prod.mk <;> existsi Identity.elim <;> intro x;
    { reflexivity }; { induction x; reflexivity }
  end

  hott def eqvEqEqv {A B C : Type u} (p : A ≃ B) (q : B = C) : A ≃ C :=
  transport (Equiv A) q p
end Equiv

def isQinv {A : Type u} {B : Type v} (f : A → B) (g : B → A) :=
(f ∘ g ~ idfun) × (g ∘ f ~ idfun)

def Qinv {A : Type u} {B : Type v} (f : A → B) :=
Σ (g : B → A), isQinv f g

namespace Qinv
  def eqv (A : Type u) (B : Type v) :=
  Σ (f : A → B), Qinv f

  hott def toBiinv {A : Type u} {B : Type v} (f : A → B) (q : Qinv f) : Equiv.biinv f :=
  (⟨q.1, q.2.2⟩, ⟨q.1, q.2.1⟩)

  hott def linvInv {A : Type u} {B : Type v}
    (f : A → B) (g : B → A) (h : B → A)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : g ∘ f ~ id :=
  let F₁ := λ x, H (g (f x));
  let F₂ := λ x, Id.map h (G (f x));
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ H x

  hott def rinvInv {A : Type u} {B : Type v}
    (f : A → B) (g : B → A) (h : B → A)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : f ∘ h ~ id :=
  let F₁ := λ x, Id.map (f ∘ h) (G x);
  let F₂ := λ x, Id.map f (H (g x));
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ G x

  hott def ofBiinv {A : Type u} {B : Type v} (f : A → B) (F : Equiv.biinv f) : Qinv f :=
  ⟨F.2.1, (F.2.2, linvInv f F.2.1 F.1.1 F.2.2 F.1.2)⟩

  hott def inv {A : Type u} {B : Type v} (e : eqv A B) : eqv B A :=
  ⟨e.2.1, ⟨e.1, (e.2.2.2, e.2.2.1)⟩⟩

  hott def toEquiv {A : Type u} {B : Type v} (e : eqv A B) : A ≃ B :=
  ⟨e.1, (⟨e.2.1, e.2.2.2⟩, ⟨e.2.1, e.2.2.1⟩)⟩
end Qinv

namespace Equiv
  hott def forwardLeft {A : Type u} {B : Type v} (e : A ≃ B) : e.forward ∘ e.left ~ idfun :=
  begin apply Qinv.rinvInv; apply e.forwardRight; apply e.leftForward end

  hott def rightForward {A : Type u} {B : Type v} (e : A ≃ B) : e.right ∘ e.forward ~ idfun :=
  begin apply Qinv.linvInv; apply e.forwardRight; apply e.leftForward end

  hott def symm {A : Type u} {B : Type v} (f : A ≃ B) : B ≃ A :=
  Qinv.toEquiv (Qinv.inv ⟨f.1, Qinv.ofBiinv f.1 f.2⟩)

  instance : @Symmetric (Type u) (· ≃ ·) := ⟨@Equiv.symm⟩

  hott def eqvInj {A : Type u} {B : Type v} (e : A ≃ B)
    (x y : A) (p : e.forward x = e.forward y) : x = y :=
  begin
    transitivity; symmetry; apply e.leftForward;
    transitivity; apply Id.map e.left;
    exact p; apply e.leftForward
  end

  hott def eqvLeftInj {A : Type u} {B : Type v} (e : A ≃ B)
    (x y : B) (p : e.left x = e.left y) : x = y :=
  begin
    transitivity; symmetry; apply e.forwardLeft;
    transitivity; apply Id.map e.forward;
    exact p; apply e.forwardLeft
  end

  hott def eqvRightInj {A : Type u} {B : Type v} (e : A ≃ B)
    (x y : B) (p : e.right x = e.right y) : x = y :=
  begin
    transitivity; symmetry; apply e.forwardRight;
    transitivity; apply Id.map e.forward;
    exact p; apply e.forwardRight
  end
end Equiv

-- half adjoint equivalence
def Ishae {A : Type u} {B : Type v} (f : A → B) :=
Σ (g : B → A) (η : g ∘ f ~ id) (ϵ : f ∘ g ~ id), Π x, Id.map f (η x) = ϵ (f x)

def fib {A : Type u} {B : Type v} (f : A → B) (y : B) := Σ (x : A), f x = y
def total {A : Type u} (B : A → Type v) := Σ x, B x
def fiberwise {A : Type u} (B : A → Type v) := Π x, B x

end GroundZero.Types