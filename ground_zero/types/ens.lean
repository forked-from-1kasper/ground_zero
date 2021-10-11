import ground_zero.theorems.prop
open ground_zero.structures

namespace ground_zero

hott theory

namespace types
universes u v w

def ens (α : Type u) : Type (max u (v + 1)) :=
Σ (φ : α → Type v), Π x, prop (φ x)

def ens.contains {α : Type u} (x : α) (s : ens α) : Type v := s.fst x
infix ` ∈ ` := ens.contains

def ens.prop {α : Type u} (x : α) (s : ens α) : prop (x ∈ s) := s.snd x
def ens.subtype {α : Type u} (s : ens α) := Σ x, s.fst x

@[hott] def ens.univ (α : Type u) : ens α :=
⟨λ _, 𝟏, λ _, unit_is_prop⟩

@[hott] def ens.union {α : Type u} (a b : ens α) : ens α :=
⟨λ x, ∥(x ∈ a) + (x ∈ b)∥, λ _, HITs.merely.uniq⟩

@[hott] def ens.sunion {α : Type u} (φ : ens.{u v} α → Type w) : ens α :=
⟨λ x, ∥(Σ (s : ens.{u v} α), x ∈ s × φ s)∥, λ _, HITs.merely.uniq⟩

@[hott] def ens.iunion {α : Type u} {β : Type v} (φ : α → ens β) : ens β :=
⟨λ x, ∥(Σ y, x ∈ φ y)∥, λ _, HITs.merely.uniq⟩
prefix `⋃`:110 := ens.iunion

instance {α : Type u} : has_union (ens α) := ⟨ens.union⟩

@[hott] def ens.inter {α : Type u} (a b : ens α) : ens α :=
⟨λ x, x ∈ a × x ∈ b, begin
  intro x, apply structures.product_prop; apply ens.prop
end⟩

instance {α : Type u} : has_inter (ens α) := ⟨ens.inter⟩

@[hott] def ens.smallest {α : Type u} (φ : ens.{u v} α → Type w) : ens α :=
⟨λ x, ∀ (s : ens.{u v} α), φ s → x ∈ s, λ y, begin
  apply structures.pi_prop, intro φ,
  apply structures.impl_prop, apply ens.prop
end⟩

def ens.inf_inter {α : Type u} (φ : ens (ens α)) : ens α := ens.smallest φ.fst

def ens.ssubset {α : Type u} (φ : ens.{u v} α) (ψ : ens.{u w} α) :=
Π x, x ∈ φ → x ∈ ψ
infix ⊆ := ens.ssubset

@[hott] def ens.ssubset.prop {α : Type u}
  (φ : ens.{u v} α) (ψ : ens.{u w} α) : prop (φ ⊆ ψ) :=
begin apply pi_prop, intro x, apply impl_prop, apply ens.prop end

@[hott, refl] def ens.ssubset.refl {α : Type u} (φ : ens α) : φ ⊆ φ :=
begin intros x, apply id end

@[hott, trans] def ens.ssubset.trans {α : Type u} {a b c : ens α} :
  a ⊆ b → b ⊆ c → a ⊆ c :=
λ G H x p, H x (G x p)

@[hott] def ens.image {α : Type u} {β : Type v} (φ : ens α) (f : α → β) : ens β :=
⟨λ y, ∥(Σ x, f x = y × x ∈ φ)∥, λ _, HITs.merely.uniq⟩

@[hott] noncomputable def ens.ext {α : Type u} {φ ψ : ens α}
  (H : Π x, x ∈ φ ↔ x ∈ ψ) : φ = ψ :=
begin
  fapply sigma.prod; apply theorems.funext; intro x,
  { apply ground_zero.ua, apply structures.prop_equiv_lemma,
    apply φ.snd, apply ψ.snd, apply (H x).left, apply (H x).right },
  { apply prop_is_prop }
end

@[hott] noncomputable def ens.ssubset.asymm {α : Type u} {φ ψ : ens α}
  (f : φ ⊆ ψ) (g : ψ ⊆ φ) : φ = ψ :=
ens.ext (λ x, ⟨f x, g x⟩)

@[hott] def ens.hset {α : Type u} (s : ens α) : hset α → hset s.subtype :=
begin
  intro H, apply hset_respects_sigma,
  { intros a b, apply H },
  { intro x, apply prop_is_set, apply s.snd }
end

@[hott] def predicate (α : Type u) := α → propset.{v}
@[hott] def ens.eqv_predicate {α : Type u} : ens α ≃ predicate α :=
begin
  fapply sigma.mk,
  { intros φ x, existsi φ.fst x, apply φ.snd },
  apply qinv.to_biinv, fapply sigma.mk,
  { intro φ, existsi (λ x, (φ x).fst), intro x, apply (φ x).snd },
  split; intro φ,
  { apply theorems.funext, intro x,
    apply theorems.prop.propset.Id, reflexivity },
  { fapply types.sigma.prod; apply theorems.funext; intro x,
    { reflexivity }, { apply prop_is_prop } }
end

@[hott] noncomputable def ens.isset {α : Type u} : hset (ens α) :=
begin
  apply hset_respects_equiv, symmetry, apply ens.eqv_predicate,
  apply pi_hset, intro x, apply theorems.prop.propset_is_set
end

@[hott] def ens.inh {α : Type u} (φ : ens α) := ∥φ.subtype∥

end types
end ground_zero