import ground_zero.algebra.reals
open ground_zero.structures (hset zero_eqv_set)
open ground_zero.HITs (trunc)
open ground_zero.types
open ground_zero

hott theory

namespace ground_zero.HITs
  universes u v w

  inductive D.core (α : Type u)
  | ε : α → D.core
  | ρ : (I → α) → (𝕀 → D.core)

  inductive D.rel (α : Type u) : D.core α → D.core α → Type u
  | η₀ (φ : I → α)    : D.rel (D.core.ρ φ 0) (D.core.ε (φ 0))
  | η₁ (φ : I → α)    : D.rel (D.core.ρ φ 1) (D.core.ε (φ 1))
  | ι (a : α) (r : 𝕀) : D.rel (D.core.ρ (λ _, a) r) (D.core.ε a)

  def D (α : Type u) := ∥graph (D.rel α)∥₀

  def D.ε {α : Type u} : α → D α := trunc.elem ∘ graph.elem ∘ D.core.ε
  def D.ρ {α : Type u} (φ : I → α) : 𝕀 → D α := trunc.elem ∘ graph.elem ∘ D.core.ρ φ

  noncomputable def D.η₀ {α : Type u} (φ : I → α) : D.ρ φ 0 = D.ε (φ 0) := trunc.elem # (graph.line (D.rel.η₀ φ))
  noncomputable def D.η₁ {α : Type u} (φ : I → α) : D.ρ φ 1 = D.ε (φ 1) := trunc.elem # (graph.line (D.rel.η₁ φ))

  def D.ι {α : Type u} (a : α) (r : 𝕀) : D.ρ (λ _, a) r = D.ε a := trunc.elem # (graph.line (D.rel.ι a r))

  @[hott] noncomputable def D.hset (α : Type u) : hset (D α) :=
  λ _ _, zero_eqv_set.forward (trunc.uniq 0)

  @[hott] noncomputable def D.ind {α : Type u} {β : D α → Type v}
    (ε : Π x, β (D.ε x)) (ρ : Π (φ : I → α) (r : 𝕀), β (D.ρ φ r))
    (η₀ : Π (φ : I → α), ρ φ 0 =[D.η₀ φ] ε (φ 0))
    (η₁ : Π (φ : I → α), ρ φ 1 =[D.η₁ φ] ε (φ 1))
    (ι : Π (a : α) (r : 𝕀), ρ (λ _, a) r =[D.ι a r] ε a)
    (H : Π x, hset (β x)) : Π x, β x :=
  begin
    fapply trunc.ind, fapply graph.ind,
    { fapply D.core.rec, apply ε, apply ρ },
    { intros x y R, induction R with φ ψ; change _ = _,
      transitivity, apply equiv.transport_comp, apply η₀,
      transitivity, apply equiv.transport_comp, apply η₁,
      transitivity, apply equiv.transport_comp, apply ι },
    { intro x, apply zero_eqv_set.right, apply H }
  end

  @[hott] noncomputable def D.rec {α : Type u} {β : Type v}
    (ε : α → β) (ρ : (I → α) → 𝕀 → β)
    (η₀ : Π (φ : I → α), ρ φ 0 = ε (φ 0))
    (η₁ : Π (φ : I → α), ρ φ 1 = ε (φ 1))
    (ι : Π a r, ρ (λ _, a) r = ε a) (H : hset β) : D α → β :=
  begin
    apply @D.ind α (λ _, β) ε ρ,
    intro φ, apply equiv.pathover_of_eq, exact η₀ φ,
    intro ψ, apply equiv.pathover_of_eq, exact η₁ ψ,
    intros a r, apply equiv.pathover_of_eq, apply ι,
    intros x y z, apply H
  end

  @[hott] def hset_path {α : Type u} (H : hset α) (φ : I → α) : φ = (λ _, φ 0) :=
  begin
    apply ground_zero.theorems.funext, fapply interval.ind,
    reflexivity, exact φ # HITs.interval.seg⁻¹, apply H
  end

  @[hott] noncomputable def D.triv {α : Type u} (H : hset α) : D α ≃ α :=
  begin
    fapply sigma.mk, fapply D.rec, exact proto.idfun,
    { intros φ r, exact φ 0 }, { intro φ, reflexivity },
    { intro φ, apply Id.map φ, exact HITs.interval.seg },
    { intros a r, reflexivity }, { intros x y, exact H }, split; existsi D.ε,
    { fapply D.ind, { intro x, reflexivity },
      { intros φ r, change D.ε (φ 0) = _, symmetry,
        transitivity, apply Id.map (λ ψ, D.ρ ψ r),
        apply hset_path (λ _ _, H), apply D.ι },
      iterate 3 { intros, apply D.hset }, intro x,
      apply ground_zero.structures.prop_is_set, apply D.hset },
    { intro x, reflexivity }
  end

  @[hott] noncomputable def D.idempotent (α : Type u) : D (D α) ≃ D α :=
  D.triv (λ _ _, D.hset α)
end ground_zero.HITs