import ground_zero.algebra.reals
open ground_zero.structures (hset zero_eqv_set)
open ground_zero.HITs (trunc)
open ground_zero.types

hott theory

namespace ground_zero.HITs
  universes u v

  inductive D.core (α : Type u)
  | ε : α → D.core
  | ρ : (I → α) → (𝕀 → D.core)

  inductive D.rel (α : Type u) : D.core α → D.core α → Type u
  | η₀ (φ : I → α) : D.rel (D.core.ρ φ 0) (D.core.ε (φ 0))
  | η₁ (φ : I → α) : D.rel (D.core.ρ φ 1) (D.core.ε (φ 1))

  def D (α : Type u) := ∥graph (D.rel α)∥₀

  def D.ε {α : Type u} : α → D α := trunc.elem ∘ graph.elem ∘ D.core.ε
  def D.ρ {α : Type u} (φ : I → α) : 𝕀 → D α := trunc.elem ∘ graph.elem ∘ D.core.ρ φ

  noncomputable def D.η₀ {α : Type u} (φ : I → α) : D.ρ φ 0 = D.ε (φ 0) := trunc.elem # (graph.line (D.rel.η₀ φ))
  noncomputable def D.η₁ {α : Type u} (φ : I → α) : D.ρ φ 1 = D.ε (φ 1) := trunc.elem # (graph.line (D.rel.η₁ φ))

  @[hott] noncomputable def D.ind {α : Type u} {β : D α → Type v}
    (ε : Π x, β (D.ε x)) (ρ : Π (φ : I → α) (r : 𝕀), β (D.ρ φ r))
    (η₀ : Π (φ : I → α), ρ φ 0 =[D.η₀ φ] ε (φ 0))
    (η₁ : Π (φ : I → α), ρ φ 1 =[D.η₁ φ] ε (φ 1))
    (H : Π x, hset (β x)) : Π x, β x :=
  begin
    fapply trunc.ind, fapply graph.ind,
    { fapply D.core.rec, apply ε, apply ρ },
    { intros x y R, induction R with φ ψ; change _ = _,
      transitivity, apply equiv.transport_comp, apply η₀,
      transitivity, apply equiv.transport_comp, apply η₁ },
    { intro x, apply zero_eqv_set.right, apply H }
  end

end ground_zero.HITs