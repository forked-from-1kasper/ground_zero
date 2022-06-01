import GroundZero.Theorems.Prop
open GroundZero.Structures

namespace GroundZero

namespace Types
universe u v w

def Ens (α : Type u) : Type (max u (v + 1)) :=
Σ (φ : α → Type v), Π x, prop (φ x)

def Ens.contains {α : Type u} (x : α) (s : Ens α) : Type v := s.1 x
infix:50 " ∈ " => Ens.contains

def Ens.prop {α : Type u} (x : α) (s : Ens α) : prop (x ∈ s) := s.2 x
def Ens.subtype {α : Type u} (s : Ens α) := Σ x, s.1 x

hott def Ens.univ (α : Type u) : Ens α :=
⟨λ _, 𝟏, λ _, unitIsProp⟩

hott def Ens.empty (α : Type u) : Ens α :=
⟨λ _, 𝟎, λ _, emptyIsProp⟩

notation "∅" => Ens.empty _

hott def Ens.union {α : Type u} (a b : Ens α) : Ens α :=
⟨λ x, ∥(x ∈ a) + (x ∈ b)∥, λ _, HITs.Merely.uniq⟩
infixl:60 " ∪ " => Ens.union

hott def Ens.sunion {α : Type u} (φ : Ens.{u, v} α → Type w) : Ens α :=
⟨λ x, ∥(Σ (s : Ens.{u, v} α), x ∈ s × φ s)∥, λ _, HITs.Merely.uniq⟩

hott def Ens.iunion {α : Type u} {β : Type v} (φ : α → Ens β) : Ens β :=
⟨λ x, ∥(Σ y, x ∈ φ y)∥, λ _, HITs.Merely.uniq⟩
prefix:110 "⋃" => Ens.iunion

hott def Ens.inter {α : Type u} (a b : Ens α) : Ens α :=
⟨λ x, x ∈ a × x ∈ b, begin intro; apply Structures.productProp <;> apply Ens.prop end⟩
infixl:60 " ∩ " => Ens.inter

hott def Ens.smallest {α : Type u} (φ : Ens.{u, v} α → Type w) : Ens α :=
⟨λ x, ∀ (s : Ens.{u, v} α), φ s → x ∈ s, λ y, begin
  apply Structures.piProp; intro;
  apply Structures.implProp; apply Ens.prop
end⟩

hott def Ens.infInter {α : Type u} (φ : Ens (Ens α)) : Ens α := Ens.smallest φ.1

hott def Ens.ssubset {α : Type u} (φ : Ens.{u, v} α) (ψ : Ens.{u, w} α) :=
Π x, x ∈ φ → x ∈ ψ

infix:50 " ⊆ " => Ens.ssubset

hott def Ens.ssubset.prop {α : Type u} (φ : Ens.{u, v} α) (ψ : Ens.{u, w} α) : Structures.prop (φ ⊆ ψ) :=
begin apply piProp; intro; apply implProp; apply Ens.prop end

hott def Ens.ssubset.refl {α : Type u} (φ : Ens α) : φ ⊆ φ :=
begin intro; apply id end

hott def Ens.ssubset.trans {α : Type u} {a b c : Ens α} : a ⊆ b → b ⊆ c → a ⊆ c :=
λ G H x p, H x (G x p)

instance {α : Type u} : @Reflexive  (Ens α) (· ⊆ ·) := ⟨Ens.ssubset.refl⟩
instance {α : Type u} : @Transitive (Ens α) (· ⊆ ·) := ⟨@Ens.ssubset.trans α⟩

hott def Ens.parallel {α : Type u} (a b : Ens α) := a ∩ b ⊆ ∅

hott def Ens.image {α : Type u} {β : Type v} (φ : Ens α) (f : α → β) : Ens β :=
⟨λ y, ∥(Σ x, f x = y × x ∈ φ)∥, λ _, HITs.Merely.uniq⟩

noncomputable hott def Ens.ext {α : Type u} {φ ψ : Ens α}
  (H : Π x, x ∈ φ ↔ x ∈ ψ) : φ = ψ :=
begin
  fapply Sigma.prod; apply Theorems.funext; intro x;
  { apply GroundZero.ua; apply Structures.propEquivLemma;
    apply φ.2; apply ψ.2; apply (H x).left; apply (H x).right };
  { apply piProp; intro; apply propIsProp }
end

noncomputable hott def Ens.ssubset.asymm {α : Type u} {φ ψ : Ens α}
  (f : φ ⊆ ψ) (g : ψ ⊆ φ) : φ = ψ :=
Ens.ext (λ x, ⟨f x, g x⟩)

hott def Ens.hset {α : Type u} (s : Ens α) (H : hset α) : hset s.subtype :=
begin
  apply hsetRespectsSigma; apply H;
  { intro; apply propIsSet; apply s.2 }
end

hott def predicate (α : Type u) := α → propset.{v}

hott def Ens.eqvPredicate {α : Type u} : Ens α ≃ predicate α :=
begin
  fapply Sigma.mk; { intros φ x; existsi φ.1 x; apply φ.2 }; apply Qinv.toBiinv; fapply Sigma.mk;
  { intro φ; existsi (λ x, (φ x).1); intro x; apply (φ x).2 }; fapply Prod.mk <;> intro φ;
  { apply Theorems.funext; intro; apply Theorems.Prop.propset.Id; reflexivity };
  { fapply Sigma.prod <;> apply Theorems.funext <;> intro x; reflexivity; apply propIsProp }
end

noncomputable hott def Ens.isset {α : Type u} : Structures.hset (Ens α) :=
begin
  apply hsetRespectsEquiv; symmetry; apply Ens.eqvPredicate;
  apply piHset; intro; apply Theorems.Prop.propsetIsSet
end

hott def Ens.inh {α : Type u} (φ : Ens α) := ∥φ.subtype∥

hott def Ens.singleton {α : Type u} (H : Structures.hset α) (x : α) : Ens α :=
⟨λ y, x = y, @H x⟩

hott def Ens.singletonInh {α : Type u} (H : Structures.hset α) (x : α) : Ens.inh (Ens.singleton @H x) :=
HITs.Merely.elem ⟨x, Id.refl⟩

end Types
end GroundZero