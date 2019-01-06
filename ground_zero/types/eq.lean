import ground_zero.proto ground_zero.meta.hott_theory
import hott.init.meta.support

namespace ground_zero.types

universes u v

theorem K {α : Sort u} {a b : α} (p q : a = b) : p = q :=
by trivial

inductive eq {α : Sort u} (a : α) : α → Sort u
| refl : eq a
attribute [refl] eq.refl

hott theory
notation a ` = ` b ` :> ` α := @eq α a b

/- fails!
theorem K₁ {α : Sort u} {a b : α} (p q : a = b :> α) :
  p = q :> (a = b :> α) :=
by trivial
-/

namespace eq
  @[inline] def rfl {α : Sort u} {a : α} : a = a :> α :=
  eq.refl a

  @[trans] def trans {α : Sort u} {a b c : α}
    (p : a = b :> α) (q : b = c :> α) : a = c :> α :=
  begin induction p, assumption end

  @[symm] def symm {α : Sort u} {a b : α} (p : a = b :> α) :
    b = a :> α :=
  begin induction p, reflexivity end

  infixr ` ⬝ ` := trans
  postfix ⁻¹ := symm

  def comp_inv {α : Sort u} {a b : α} (p : a = b :> α) :
    p ⬝ p⁻¹ = eq.refl a :> a = a :> α :=
  begin induction p, trivial end

  def inv_comp {α : Sort u} {a b : α} (p : a = b :> α) :
    p⁻¹ ⬝ p = eq.refl b :> b = b :> α :=
  begin induction p, trivial end

  def refl_left {α : Sort u} {a b : α} (p : a = b :> α) :
    eq.refl a ⬝ p = p :> a = b :> α :=
  begin induction p, trivial end

  def refl_right {α : Sort u} {a b : α} (p : a = b :> α) :
    p ⬝ eq.refl b = p :> a = b :> α :=
  begin induction p, trivial end

  def refl_twice {α : Sort u} {a b : α} (p : a = b :> α) :
    rfl ⬝ p ⬝ rfl = p :> a = b :> α :=
  begin induction p, trivial end

  def assoc {α : Sort u} {a b c d : α}
    (p : a = b :> α) (q : b = c :> α) (r : c = d :> α) :
    p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r := begin
    induction p, induction q, induction r,
    trivial
  end

  def mpr {α β : Sort u} (p : α = β) : β → α :=
  begin induction p, intro x, exact x end

  def map {α : Sort u} {β : Sort v} {a b : α}
    (f : α → β) (p : a = b :> α) : f a = f b :> β :=
  begin induction p, reflexivity end
  infix [parsing_only] ` # ` := map

  def ap₂ {α : Sort u} {β : Sort v} {a b : α}
    {p q : a = b :> α} (f : α → β)
    (r : p = q :> a = b :> α) :
    f # p = f # q :> f a = f b :> β :=
  begin induction r, reflexivity end

  class dotted (space : Sort u) :=
  (point : space)

  structure pointed :=
  (space : Sort u) (point : space)

  def loop_space (X : pointed) : pointed :=
  ⟨X.point = X.point :> X.space, eq.refl X.point⟩

  def iterated_loop_space : pointed → ℕ → pointed
  | X 0 := X
  | X (n + 1) := iterated_loop_space (loop_space X) n

  def loop_pointed_space (α : Sort u) [h : dotted α] :=
  iterated_loop_space ⟨α, dotted.point α⟩

  notation `Ω` `[` n `]` `, ` X := (iterated_loop_space X n).space
  notation `Θ` `[` n `]` `, ` X := (iterated_loop_space X n).point

  notation `Ω¹` X := (loop_pointed_space X 1).space
end eq

namespace not
  notation `¬` a := a → empty
  notation a ` ≠ ` b := ¬(a = b :> _)
end not

namespace whiskering
  variables {α : Sort u} {a b c : α}
  variables {p q : a = b :> α} {r s : b = c :> α}
  variables {ν : p = q} {κ : r = s}

  def right_whs (ν : p = q) (r : b = c) : p ⬝ r = q ⬝ r := begin
    induction r,
    exact (eq.refl_right p) ⬝ ν ⬝ (eq.refl_right q)⁻¹
  end
  infix ` ⬝ᵣ `:60 := right_whs

  def left_whs (q : a = b) (κ : r = s) : q ⬝ r = q ⬝ s := begin
    induction q,
    exact (eq.refl_left r) ⬝ κ ⬝ (eq.refl_left s)⁻¹
  end
  infix ` ⬝ₗ `:60 := left_whs

  def horizontal_comp₁ (ν : p = q) (κ : r = s) :=
  (ν ⬝ᵣ r) ⬝ (q ⬝ₗ κ)
  infix ` ⋆ `:65 := horizontal_comp₁

  def horizontal_comp₂ (ν : p = q) (κ : r = s) :=
  (p ⬝ₗ κ) ⬝ (ν ⬝ᵣ s)
  infix ` ⋆′ `:65 := horizontal_comp₂

  lemma comp_uniq : ν ⋆ κ = ν ⋆′ κ := begin
    induction p, induction r, induction ν, induction κ,
    reflexivity
  end

  lemma loop₁ {α : Sort u} {a : α}
    {ν κ : eq.refl a = eq.refl a} :
    ν ⬝ κ = ν ⋆ κ := begin
    symmetry, unfold horizontal_comp₁,
    unfold right_whs, unfold left_whs,
    transitivity,
    { apply eq.map, apply eq.refl_twice },
    apply eq.map (λ p, p ⬝ κ), apply eq.refl_twice
  end

  lemma loop₂ {α : Sort u} {a : α}
    {ν κ : eq.refl a = eq.refl a} :
    ν ⋆′ κ = κ ⬝ ν := begin
    unfold horizontal_comp₂,
    unfold right_whs, unfold left_whs,
    transitivity,
    { apply eq.map, apply eq.refl_twice },
    apply eq.map (λ p, p ⬝ ν), apply eq.refl_twice
  end

  theorem «Eckmann–Hilton argument» {α : Sort u} {a : α}
    (ν κ : eq.refl a = eq.refl a) : ν ⬝ κ = κ ⬝ ν :=
  loop₁ ⬝ comp_uniq ⬝ loop₂
end whiskering

end ground_zero.types