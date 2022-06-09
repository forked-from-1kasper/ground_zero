import GroundZero.Theorems.Equiv
open GroundZero.Structures

namespace GroundZero

namespace Types
universe u v w

def Ens (A : Type u) : Type (max u (v + 1)) :=
Σ (φ : A → Type v), Π x, prop (φ x)

def Ens.contains {A : Type u} (x : A) (s : Ens A) : Type v := s.1 x
infix:80 (priority := high) " ∈ " => Ens.contains

def Ens.prop {A : Type u} (x : A) (s : Ens A) : prop (x ∈ s) := s.2 x
def Ens.subtype {A : Type u} (s : Ens A) := Σ x, s.1 x

hott def Ens.univ (A : Type u) : Ens A :=
⟨λ _, 𝟏, λ _, unitIsProp⟩

hott def Ens.empty (A : Type u) : Ens A :=
⟨λ _, 𝟎, λ _, emptyIsProp⟩

notation "∅" => Ens.empty _

hott def Ens.union {A : Type u} (a b : Ens A) : Ens A :=
⟨λ x, ∥(x ∈ a) + (x ∈ b)∥, λ _, HITs.Merely.uniq⟩
infixl:60 " ∪ " => Ens.union

hott def Ens.sunion {A : Type u} (φ : Ens.{u, v} A → Type w) : Ens A :=
⟨λ x, ∥(Σ (s : Ens.{u, v} A), x ∈ s × φ s)∥, λ _, HITs.Merely.uniq⟩

hott def Ens.iunion {A : Type u} {β : Type v} (φ : A → Ens β) : Ens β :=
⟨λ x, ∥(Σ y, x ∈ φ y)∥, λ _, HITs.Merely.uniq⟩
prefix:110 "⋃" => Ens.iunion

hott def Ens.inter {A : Type u} (a b : Ens A) : Ens A :=
⟨λ x, x ∈ a × x ∈ b, begin intro; apply Structures.productProp <;> apply Ens.prop end⟩
infixl:60 " ∩ " => Ens.inter

hott def Ens.smallest {A : Type u} (φ : Ens.{u, v} A → Type w) : Ens A :=
⟨λ x, ∀ (s : Ens.{u, v} A), φ s → x ∈ s, λ y, begin
  apply Structures.piProp; intro;
  apply Structures.implProp; apply Ens.prop
end⟩

hott def Ens.infInter {A : Type u} (φ : Ens (Ens A)) : Ens A := Ens.smallest φ.1

hott def Ens.ssubset {A : Type u} (φ : Ens.{u, v} A) (ψ : Ens.{u, w} A) :=
Π x, x ∈ φ → x ∈ ψ

infix:50 " ⊆ " => Ens.ssubset

hott def Ens.ssubset.prop {A : Type u} (φ : Ens.{u, v} A) (ψ : Ens.{u, w} A) : Structures.prop (φ ⊆ ψ) :=
begin apply piProp; intro; apply implProp; apply Ens.prop end

hott def Ens.ssubset.refl {A : Type u} (φ : Ens A) : φ ⊆ φ :=
begin intro; apply id end

hott def Ens.ssubset.trans {A : Type u} {a b c : Ens A} : a ⊆ b → b ⊆ c → a ⊆ c :=
λ G H x p, H x (G x p)

instance {A : Type u} : @Reflexive  (Ens A) (· ⊆ ·) := ⟨Ens.ssubset.refl⟩
instance {A : Type u} : @Transitive (Ens A) (· ⊆ ·) := ⟨@Ens.ssubset.trans A⟩

hott def Ens.parallel {A : Type u} (a b : Ens A) := a ∩ b ⊆ ∅

hott def Ens.image {A : Type u} {β : Type v} (φ : Ens A) (f : A → β) : Ens β :=
⟨λ y, ∥(Σ x, f x = y × x ∈ φ)∥, λ _, HITs.Merely.uniq⟩

noncomputable hott def Ens.ext {A : Type u} {φ ψ : Ens A}
  (H : Π x, x ∈ φ ↔ x ∈ ψ) : φ = ψ :=
begin
  fapply Sigma.prod; apply Theorems.funext; intro x;
  { apply GroundZero.ua; apply Structures.propEquivLemma;
    apply φ.2; apply ψ.2; apply (H x).left; apply (H x).right };
  { apply piProp; intro; apply propIsProp }
end

noncomputable hott def Ens.ssubset.asymm {A : Type u} {φ ψ : Ens A}
  (f : φ ⊆ ψ) (g : ψ ⊆ φ) : φ = ψ :=
Ens.ext (λ x, ⟨f x, g x⟩)

hott def Ens.hset {A : Type u} (s : Ens A) (H : hset A) : hset s.subtype :=
begin
  apply hsetRespectsSigma; apply H;
  { intro; apply propIsSet; apply s.2 }
end

hott def predicate (A : Type u) := A → propset.{v}

hott def Ens.eqvPredicate {A : Type u} : Ens A ≃ predicate A :=
begin
  fapply Sigma.mk; { intros φ x; existsi φ.1 x; apply φ.2 }; apply Qinv.toBiinv; fapply Sigma.mk;
  { intro φ; existsi (λ x, (φ x).1); intro x; apply (φ x).2 }; fapply Prod.mk <;> intro φ;
  { apply Theorems.funext; intro; apply Theorems.Equiv.propset.Id; reflexivity };
  { fapply Sigma.prod <;> apply Theorems.funext <;> intro x; reflexivity; apply propIsProp }
end

noncomputable hott def Ens.isset {A : Type u} : Structures.hset (Ens A) :=
begin
  apply hsetRespectsEquiv; symmetry; apply Ens.eqvPredicate;
  apply piHset; intro; apply Theorems.Equiv.propsetIsSet
end

hott def Ens.inh {A : Type u} (φ : Ens A) := ∥φ.subtype∥

hott def Ens.singleton {A : Type u} (H : Structures.hset A) (x : A) : Ens A :=
⟨λ y, x = y, @H x⟩

hott def Ens.singletonInh {A : Type u} (H : Structures.hset A) (x : A) : Ens.inh (Ens.singleton @H x) :=
HITs.Merely.elem ⟨x, Id.refl⟩

end Types
end GroundZero