import GroundZero.Support
open GroundZero.Proto (idfun Identity Identity.elem Identity.elim)

def S (x : α → β → γ) (y : α → β) (z : α) := x z (y z)

section
  universe u v
  variable {α : Type u} {β : Type v}

  def Prod.Id {a c : α} {b d : β} (p : a = c) (q : b = d) : (a, b) = (c, d) :=
  begin induction p; induction q; reflexivity end

  def Prod.intro : α → β → α × β := Prod.mk
  def Prod.pr₁   : α × β → α     := Prod.fst
  def Prod.pr₂   : α × β → β     := Prod.snd
end

namespace GroundZero.Types
universe u v w k

namespace Equiv

  def Homotopy {α : Type u} {π : α → Type v} (f g : Π x, π x) :=
  Π (x : α), f x = g x
  infix:80 " ~ " => Homotopy

  hott def Homotopy.id {α : Type u} {π : α → Type v} (f : Π x, π x) : f ~ f :=
  begin intro x; reflexivity end

  hott def Homotopy.symm {α : Type u} {π : α → Type v}
    (f g : Π (x : α), π x) (h : f ~ g) : g ~ f :=
  λ x, (h x)⁻¹

  hott def Homotopy.trans {α : Type u} {π : α → Type v}
    {f g h : Π (x : α), π x} (p : f ~ g) (q : g ~ h) : f ~ h :=
  λ x, p x ⬝ q x

  section
    variable {α : Type u} {π : α → Type v}
    instance : @Reflexive  (Π x, π x) (· ~ ·) := ⟨@Homotopy.id α π⟩
    instance : @Symmetric  (Π x, π x) (· ~ ·) := ⟨@Homotopy.symm α π⟩
    instance : @Transitive (Π x, π x) (· ~ ·) := ⟨@Homotopy.trans α π⟩
  end

  hott def Homotopy.Id {α : Type u} {π : α → Type v}
    {f g : Π x, π x} (η : f = g) : f ~ g :=
  begin induction η; reflexivity end

  def linv {α : Type u} {β : Type v} (f : α → β) :=
  Σ (g : β → α), g ∘ f ~ idfun

  def rinv {α : Type u} {β : Type v} (f : α → β) :=
  Σ (g : β → α), f ∘ g ~ idfun

  def biinv {α : Type u} {β : Type v} (f : α → β) :=
  linv f × rinv f

  hott def homotopy_square {α : Type u} {β : Type v}
    {f g : α → β} (H : f ~ g) {x y : α} (p : x = y) :
    H x ⬝ Id.map g p = Id.map f p ⬝ H y :=
  begin induction p; transitivity; apply Id.reflRight; apply Id.reflLeft end
end Equiv

def Equiv (α : Type u) (β : Type v) : Type (max u v) :=
Σ (f : α → β), Equiv.biinv f
infix:25 " ≃ " => Equiv

namespace Equiv
  hott def forward {α : Type u} {β : Type v} (e : α ≃ β) : α → β := e.fst
  instance forwardCoe {α : Type u} {β : Type v} : CoeFun (α ≃ β) (λ _, α → β) := ⟨forward⟩

  hott def left {α : Type u} {β : Type v} (e : α ≃ β) : β → α := e.2.1.1
  hott def right {α : Type u} {β : Type v} (e : α ≃ β) : β → α := e.2.2.1

  hott def leftForward {α : Type u} {β : Type v} (e : α ≃ β) : e.left ∘ e.forward ~ id := e.2.1.2
  hott def forwardRight {α : Type u} {β : Type v} (e : α ≃ β) : e.forward ∘ e.right ~ id := e.2.2.2

  hott def id (α : Type u) : α ≃ α :=
  ⟨idfun, (⟨idfun, idp⟩, ⟨idfun, idp⟩)⟩

  instance : @Reflexive (Type u) (· ≃ ·) := ⟨id⟩

  hott def inveqv {α : Type u} {a b : α} : (a = b) ≃ (b = a) :=
  ⟨Id.inv, (⟨Id.inv, Id.invInv⟩, ⟨Id.inv, Id.invInv⟩)⟩

  hott def biinvTrans {α : Type u} {β : Type v} {γ : Type w}
    {f : α → β} {g : β → γ} (e₁ : biinv f) (e₂ : biinv g) : biinv (g ∘ f) :=
  (⟨e₁.1.1 ∘ e₂.1.1, λ x, Id.map e₁.1.1 (e₂.1.2 (f x)) ⬝ e₁.1.2 x⟩,
   ⟨e₁.2.1 ∘ e₂.2.1, λ x, Id.map g (e₁.2.2 (e₂.2.1 x)) ⬝ e₂.2.2 x⟩)

  hott def trans {α : Type u} {β : Type v} {γ : Type w}
    (f : α ≃ β) (g : β ≃ γ) : α ≃ γ :=
  ⟨g.1 ∘ f.1, biinvTrans f.2 g.2⟩

  instance : @Transitive (Type u) (· ≃ ·) := ⟨@trans⟩

  hott def idtoeqv {α β : Type u} (p : α = β) : α ≃ β :=
  begin induction p; reflexivity end

  hott def idtoiff {α β : Type u} (p : α = β) : α ↔ β :=
  begin induction p; reflexivity end

  hott def transportconst {α β : Type u} : α = β → α → β :=
  forward ∘ idtoeqv

  def transportconstInv {α β : Type u} : α = β → β → α :=
  left ∘ idtoeqv

  hott def transportconstOverInv {α β : Type u} (p : α = β) :
    Π x, transportconst p⁻¹ x = transportconstInv p x :=
  begin intro x; induction p; reflexivity end

  hott def subst {α : Type u} {π : α → Type v} {a b : α} (p : a = b) : π a → π b :=
  begin induction p; apply idfun end

  hott def happly {α : Type u} {β : Type v} {f g : α ≃ β}
    (p : f = g) : f.forward ~ g.forward :=
  begin induction p; reflexivity end

  -- subst with explicit π
  def transport {α : Type u} (π : α → Type v) {a b : α} (p : a = b) : π a → π b :=
  subst p

  def depPath {α : Type u} (π : α → Type v) {a b : α} (p : a = b) (u : π a) (v : π b) :=
  Equiv.subst p u = v

  notation u " =[" P ", " p "] " v => depPath P p u v
  notation u " =[" p "] " v       => depPath _ p u v

  hott def depPath.refl {α : Type u} (π : α → Type v) {a : α} (u : π a) : u =[idp a] u :=
  idp u

  instance {α : Type u} (π : α → Type v) (a : α) :
    @Reflexive (π a) (depPath π (idp a)) :=
  ⟨depPath.refl π⟩

  hott def pathoverOfEq {α : Type u} {β : Type v} {a b : α} {a' b' : β}
    (p : a = b) (q : a' = b') : a' =[λ _, β, p] b' :=
  begin induction p; apply q end

  hott def transportForwardAndBack {α : Type u} {β : α → Type v}
    {x y : α} (p : x = y) (u : β x) : subst p⁻¹ (subst p u) = u :=
  begin induction p; reflexivity end

  hott def transportBackAndForward {α : Type u} {β : α → Type v}
    {x y : α} (p : x = y) (u : β y) : subst p (subst p⁻¹ u) = u :=
  begin induction p; reflexivity end

  hott def depPath.symm {α : Type u} {β : α → Type v} {a b : α}
    (p : a = b) {u : β a} {v : β b} (q : u =[p] v) : v =[p⁻¹] u :=
  begin induction q using Id.casesOn; apply transportForwardAndBack end

  hott def substComp {α : Type u} {π : α → Type v} {a b c : α}
    (p : a = b) (q : b = c) (x : π a) : subst (p ⬝ q) x = subst q (subst p x) :=
  begin induction p; induction q; reflexivity end

  hott def depTrans {α : Type u} {π : α → Type v}
    {a b c : α} {p : a = b} {q : b = c} {u : π a} {v : π b} {w : π c}
    (r : u =[p] v) (s : v =[q] w): u =[p ⬝ q] w :=
  begin induction r using Id.casesOn; induction s using Id.casesOn; apply substComp end
  infix:40 " ⬝′ " => depTrans

  hott def substInv {α : Type u} {π : α → Type v} {a b : α} (p : a = b) : π b → π a :=
  begin induction p; exact idfun end

  hott def substOverPathComp {α : Type u} {π : α → Type v} {a b c : α}
    (p : a = b) (q : b = c) (x : π a) : subst (p ⬝ q) x = subst q (subst p x) :=
  begin induction p; reflexivity end

  hott def substOverInvPath {α : Type u} {π : α → Type v} {a b : α}
    (p : a = b) (x : π b) : subst p⁻¹ x = substInv p x :=
  begin induction p; reflexivity end

  hott def apd {α : Type u} {β : α → Type v} {a b : α}
    (f : Π (x : α), β x) (p : a = b) : subst p (f a) = f b :=
  begin induction p; reflexivity end

  hott def apdFunctoriality {α : Type u} {β : α → Type v} {a b c : α}
    (f : Π x, β x) (p : a = b) (q : b = c) :
    @apd α β a c f (p ⬝ q) = depTrans (apd f p) (apd f q) :=
  begin induction p; induction q; reflexivity end

  hott def substSquare {α : Type u} {π : α → Type v} {a b : α}
    {p q : a = b} (r : p = q) (u : π a) : subst p u = subst q u :=
  begin induction r; reflexivity end

  notation "subst²" => substSquare

  hott def depPathMap {α : Type u} {π : α → Type v} {δ : α → Type w} {a b : α}
    {p : a = b} {u : π a} {v : π b} (g : Π x, π x → δ x) (q : u =[p] v) : g a u =[p] g b v :=
  begin induction p; induction q using Id.casesOn; reflexivity end

  hott def depPathMap' {α : Type u} {β : Type v} {π : α → Type w} {δ : β → Type k}
    {a b : α} {p : a = b} {u : π a} {v : π b} (f : α → β)
    (g : Π x, π x → δ (f x)) (q : u =[p] v) : g a u =[Id.map f p] g b v :=
  begin induction p; induction q using Id.casesOn; apply idp end

  def transportInv {α : Type u} (π : α → Type v) {a b : α} (p : a = b) : π b → π a :=
  substInv p

  def transportSquare {α : Type u} (π : α → Type v) {a b : α}
    {p q : a = b} (r : p = q) (u : π a) : subst p u = subst q u :=
  substSquare r u

  notation "transport²" => transportSquare

  hott def transportComp {α : Type u} {β : Type v}
    (π : β → Type w) {x y : α} (f : α → β) (p : x = y) (u : π (f x)) :
    transport (π ∘ f) p u = transport π (Id.map f p) u :=
  begin induction p; reflexivity end

  hott def transportToTransportconst {α : Type u} (π : α → Type v) {a b : α}
    (p : a = b) (u : π a) : Equiv.transport π p u = Equiv.transportconst (Id.map π p) u :=
  begin induction p; reflexivity end

  hott def transportconstOverComposition {α β γ : Type u} (p : α = β) (q : β = γ)
    (x : α) : transportconst (p ⬝ q) x = transportconst q (transportconst p x) :=
  begin induction p; induction q; reflexivity end

  hott def transportComposition {α : Type u} {a x₁ x₂ : α}
    (p : x₁ = x₂) (q : a = x₁) : transport (Id a) p q = q ⬝ p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott def transportCharacterization {α : Type u} {μ η : α → Type v} {a b : α} (φ : η a → μ a)
    (p : a = b) : transport (λ x, η x → μ x) p φ = transport μ p ∘ φ ∘ transport η p⁻¹ :=
  begin induction p; reflexivity end

  hott def transportOverFamily {α : Type u} {x y : α} {π δ : α → Type v}
    (f : Π x, π x → δ x) (p : x = y) (u : π x) : subst p (f x u) = f y (subst p u) :=
  begin induction p; reflexivity end

  hott def apdSqr {α : Type u} {β γ : α → Type v} {a b : α} {u : β a} {v : β b} {p : a = b}
    (f : Π {x : α} (u : β x), γ x) (q : u =[p] v) : f u =[p] f v :=
  begin induction p; induction q using Id.casesOn; reflexivity end

  hott def apd₂ {α : Type u} {β : α → Type v} {a b : α} {p q : a = b}
    (f : Π x, β x) (r : p = q) : apd f p =[λ s, subst s (f a) = f b, r] apd f q :=
  begin induction r; reflexivity end

  hott def rewriteComp {α : Type u} {a b c : α}
    {p : a = b} {q : b = c} {r : a = c} (h : r = p ⬝ q) : p⁻¹ ⬝ r = q :=
  begin induction p; apply h end

  hott def invRewriteComp {α : Type u} {a b c : α}
    {p : a = b} {q : b = c} {r : a = c} (h : p⁻¹ ⬝ r = q) : r = p ⬝ q :=
  begin induction p; apply h end

  hott def invCompRewrite {α : Type u} {a b c : α}
    {p : a = b} {q : b = c} {r : a = c} (h : p ⬝ q = r) : p = r ⬝ q⁻¹ :=
  begin induction q; exact (Id.reflRight p)⁻¹ ⬝ h ⬝ (Id.reflRight r)⁻¹ end

  hott def pathoverFromTrans {α : Type u} {a b c : α}
    (p : b = c) (q : a = b) (r : a = c) (η : q ⬝ p = r) : q =[p] r :=
  begin induction η; apply transportComposition end

  hott def transportInvCompComp {α : Type u} {a b : α} (p : a = b) (q : a = a) :
    Equiv.transport (λ x, x = x) p q = p⁻¹ ⬝ q ⬝ p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott def mapFunctoriality {α : Type u} {β : Type v}
    {a b c : α} (f : α → β) {p : a = b} {q : b = c} :
    Id.map f (p ⬝ q) = Id.map f p ⬝ Id.map f q :=
  begin induction p; reflexivity end

  hott def transportOverContrMap {α : Type u} {β : Type v} {a b : α} {c : β}
    (f : α → β) (p : a = b) (q : f a = c) :
    Equiv.transport (λ x, f x = c) p q = Id.map f p⁻¹ ⬝ q :=
  begin induction p; reflexivity end

  hott def transportOverInvContrMap {α : Type u} {β : Type v} {a b : α} {c : β}
    (f : α → β) (p : a = b) (q : c = f a) :
    Equiv.transport (λ x, c = f x) p q = q ⬝ Id.map f p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott def transportOverInvolution {α : Type u} {a b : α} (f : α → α) (p : a = b) (q : f a = a) :
    Equiv.transport (λ x, f x = x) p q = Id.map f p⁻¹ ⬝ q ⬝ p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott def transportOverHmtpy {α : Type u} {β : Type v} {a b : α} (f g : α → β) (p : a = b) (q : f a = g a) :
    Equiv.transport (λ x, f x = g x) p q = Id.map f p⁻¹ ⬝ q ⬝ Id.map g p :=
  begin induction p; symmetry; apply Id.reflRight end

  hott def idmap {α : Type u} {a b : α} (p : a = b) : Id.map idfun p = p :=
  begin induction p; reflexivity end

  hott def constmap {α : Type u} {β : Type v} {a b : α} {c : β}
    (p : a = b) : Id.map (λ _, c) p = idp c :=
  begin induction p; reflexivity end

  hott def transportOverDhmtpy {α : Type u} {β : α → Type v} {a b : α}
    (f g : Π x, β x) (p : a = b) (q : f a = g a) :
    Equiv.transport (λ x, f x = g x) p q = (apd f p)⁻¹ ⬝ Id.map (subst p) q ⬝ apd g p :=
  begin induction p; symmetry; transitivity; apply Id.reflRight; apply idmap end

  hott def mapOverComp {α : Type u} {β : Type v} {γ : Type w} {a b : α}
    (f : α → β) (g : β → γ) (p : a = b) :
    @Id.map α γ a b (g ∘ f) p = Id.map g (Id.map f p) :=
  begin induction p; reflexivity end

  hott def apdOverConstantFamily {α : Type u} {β : Type v} {a b : α}
    (f : α → β) (p : a = b) : apd f p = pathoverOfEq p (Id.map f p) :=
  begin induction p; reflexivity end

  def reflPathover {α : Type u} {β : Type v} {a : α} {x y : β} (p : x =[λ _, β, idp a] y) : x = y := p

  hott def pathoverInv {α : Type u} {β : Type v} (a : α) {x y : β} (p : x = y) :
    reflPathover (pathoverOfEq (idp a) p) = p :=
  begin induction p; reflexivity end

  hott def pathoverOfEqInj {α : Type u} {β : Type v} {a b : α} {a' b' : β}
    (r : a = b) (p q : a' = b') (η : pathoverOfEq r p = pathoverOfEq r q) : p = q :=
  begin induction r; apply η end

  hott def transportImpl {α : Type u} (μ : α → Type v)
    (η : α → Type w) {a b : α} (p : a = b) (φ : μ a → η a) :
    transport (λ x, μ x → η x) p φ = λ x, subst p (φ (subst p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott def transportOverConstFamily {α : Type u} {β : Type v}
    {a b : α} (p : a = b) (b : β) : transport (λ _, β) p b = b :=
  begin induction p; reflexivity end

  hott def transportOverPi {α : Type u} {a b : α} {β : Type v}
    (π : α → β → Type w) (p : a = b) (u : Π y, π a y) :
    transport (λ x, Π y, π x y) p u = (λ y, @transport α (λ x, π x y) a b p (u y)) :=
  begin induction p; reflexivity end

  hott def transportOverFunction {α : Type u} {β : Type v}
    {a : α} {b : β} (f g : α → β) (p : f = g) (q : f a = b) :
    transport (λ (f' : α → β), f' a = b) p q =
    @Id.map (α → β) β g f (λ (f' : α → β), f' a) p⁻¹ ⬝ q :=
  begin induction p; reflexivity end

  hott def transportOverOperation {α β : Type u} (φ : α → α → α) (p : α = β) :
    transport (λ α, α → α → α) p φ = λ x y, transport idfun p (φ (transport idfun p⁻¹ x) (transport idfun p⁻¹ y)) :=
  begin induction p; reflexivity end

  hott def transportOverFunctor {α β : Type u} (μ : Type u → Type v) (η : Type u → Type w)
    (φ : μ α → η α) (p : α = β) : transport (λ α, μ α → η α) p φ = λ x, subst p (φ (subst p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott def transportOverMorphism {α β : Type u} (φ : α → α) (p : α = β) :
    transport (λ α, α → α) p φ = λ x, transport idfun p (φ (transport idfun p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott def transportOverOperationPointwise {α β : Type u} (φ : α → α → α) (p : α = β) {x y : β} :
      transport (λ α, α → α → α) p φ x y
    = transport idfun p (φ (transport idfun p⁻¹ x) (transport idfun p⁻¹ y)) :=
  begin induction p; reflexivity end

  hott def transportOverMorphismPointwise {α β : Type u} (φ : α → α) (p : α = β) {x : β} :
    transport (λ α, α → α) p φ x = transport idfun p (φ (transport idfun p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott def bimap {α : Type u} {β : Type v} {γ : Type w} {a b : α} {a' b' : β}
    (f : α → β → γ) (p : a = b) (q : a' = b') : f a a' = f b b' :=
  begin induction p; induction q; reflexivity end

  hott def bimapReflLeft {α : Type u} {β : Type v} {γ : Type w}
    {a : α} {a' b' : β} (f : α → β → γ) (p : a' = b') :
    bimap f (idp a) p = Id.map (f a) p :=
  begin induction p; reflexivity end

  hott def bimapReflRight {α : Type u} {β : Type v} {γ : Type w}
    {a b : α} {a' : β} (f : α → β → γ) (p : a = b) :
    bimap f p (idp a') = Id.map (f · a') p :=
  begin induction p; reflexivity end

  hott def bimapCharacterization {α : Type u} {β : Type v} {γ : Type w}
    {a b : α} {a' b' : β} (f : α → β → γ) (p : a = b) (q : a' = b') :
    bimap f p q = @Id.map α γ a b (f · a') p ⬝ Id.map (f b) q :=
  begin induction p; induction q; reflexivity end

  hott def bimapCharacterization' {α : Type u} {β : Type v} {γ : Type w}
    {a b : α} {a' b' : β} (f : α → β → γ) (p : a = b) (q : a' = b') :
    bimap f p q = Id.map (f a) q ⬝ @Id.map α γ a b (f · b') p :=
  begin induction p; induction q; reflexivity end

  hott def bimapInv {α : Type u} {β : Type v} {γ : Type w} {a b : α} {a' b' : β}
    (f : α → β → γ) (p : a = b) (q : a' = b') : (bimap f p q)⁻¹ = bimap f p⁻¹ q⁻¹ :=
  begin induction p; induction q; reflexivity end

  hott def bimapComp {α : Type u} {β : Type v} {γ : Type w}
    {a b : α} {a' b' : β} (f : α → β → γ) (p : a = b) (q : a' = b') :
    Id.map (f · a') p = Id.map (f a) q ⬝ bimap f p q⁻¹ :=
  begin
    induction p; symmetry; transitivity; apply Id.map; transitivity;
    apply bimapReflLeft; apply Id.mapInv; apply Id.compInv
  end

  hott def mapOverS {α : Type u} {a b : α} (f : α → α → α) (g : α → α) (p : a = b) :
    Id.map (S f g) p = @bimap α α α a b (g a) (g b) f p (Id.map g p) :=
  begin induction p; reflexivity end

  hott def liftedHapply {α : Type u} (μ : α → Type v) (η : α → Type w)
    {a b : α} (p : a = b) (f : μ a → η a) (g : μ b → η b)
    (q : transport (λ x, μ x → η x) p f = g) :
    Π x, transport η p (f x) = g (transport μ p x) :=
  begin induction p; induction q; intro x; reflexivity end

  hott def identityEqv {α : Type u} : α ≃ Identity α :=
  begin
    existsi Identity.elem; apply Prod.mk <;> existsi Identity.elim <;> intro x;
    { reflexivity }; { induction x; reflexivity }
  end

  hott def eqvEqEqv {α β γ : Type u} (p : α ≃ β) (q : β = γ) : α ≃ γ :=
  transport (Equiv α) q p
end Equiv

def isQinv {α : Type u} {β : Type v} (f : α → β) (g : β → α) :=
(f ∘ g ~ idfun) × (g ∘ f ~ idfun)

def Qinv {α : Type u} {β : Type v} (f : α → β) :=
Σ (g : β → α), isQinv f g

namespace Qinv
  def eqv (α : Type u) (β : Type v) :=
  Σ (f : α → β), Qinv f

  hott def toBiinv {α : Type u} {β : Type v} (f : α → β) (q : Qinv f) : Equiv.biinv f :=
  (⟨q.1, q.2.2⟩, ⟨q.1, q.2.1⟩)

  hott def linvInv {α : Type u} {β : Type v}
    (f : α → β) (g : β → α) (h : β → α)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : g ∘ f ~ id :=
  let F₁ := λ x, H (g (f x));
  let F₂ := λ x, Id.map h (G (f x));
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ H x

  hott def rinvInv {α : Type u} {β : Type v}
    (f : α → β) (g : β → α) (h : β → α)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : f ∘ h ~ id :=
  let F₁ := λ x, Id.map (f ∘ h) (G x);
  let F₂ := λ x, Id.map f (H (g x));
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ G x

  hott def ofBiinv {α : Type u} {β : Type v} (f : α → β) (F : Equiv.biinv f) : Qinv f :=
  ⟨F.2.1, (F.2.2, linvInv f F.2.1 F.1.1 F.2.2 F.1.2)⟩

  hott def inv {α : Type u} {β : Type v} (e : eqv α β) : eqv β α :=
  ⟨e.2.1, ⟨e.1, (e.2.2.2, e.2.2.1)⟩⟩

  hott def toEquiv {α : Type u} {β : Type v} (e : eqv α β) : α ≃ β :=
  ⟨e.1, (⟨e.2.1, e.2.2.2⟩, ⟨e.2.1, e.2.2.1⟩)⟩
end Qinv

hott def Equiv.forwardFeft {α : Type u} {β : Type v} (e : α ≃ β) : e.forward ∘ e.left ~ idfun :=
begin apply Qinv.rinvInv; apply e.forwardRight; apply e.leftForward end

hott def Equiv.rightForward {α : Type u} {β : Type v} (e : α ≃ β) : e.right ∘ e.forward ~ idfun :=
begin apply Qinv.linvInv; apply e.forwardRight; apply e.leftForward end

hott def Equiv.symm {α : Type u} {β : Type v} (f : α ≃ β) : β ≃ α :=
Qinv.toEquiv (Qinv.inv ⟨f.1, Qinv.ofBiinv f.1 f.2⟩)

instance : @Symmetric (Type u) (· ≃ ·) := ⟨@Equiv.symm⟩

-- half adjoint equivalence
def Ishae {α : Type u} {β : Type v} (f : α → β) :=
Σ (g : β → α) (η : g ∘ f ~ id) (ϵ : f ∘ g ~ id), Π x, Id.map f (η x) = ϵ (f x)

def fib {α : Type u} {β : Type v} (f : α → β) (y : β) := Σ (x : α), f x = y
def total {α : Type u} (β : α → Type v) := Σ x, β x
def fiberwise {α : Type u} (β : α → Type v) := Π x, β x

end GroundZero.Types