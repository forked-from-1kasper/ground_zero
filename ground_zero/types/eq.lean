import ground_zero.proto ground_zero.meta.hott_theory

namespace ground_zero.types
universes u v

theorem UIP {α : Type u} {a b : α} (p q : a = b) : p = q :=
by trivial

inductive eq {α : Type u} (a : α) : α → Type u
| refl : eq a

attribute [hott, refl] eq.refl

hott theory
notation a ` = ` b ` :> ` α := @eq α a b

/- fails!
theorem UIP₁ {α : Type u} {a b : α} (p q : a = b :> α) :
  p = q :> (a = b :> α) :=
by trivial
-/

abbreviation idp {α : Type u} (a : α) : a = a :> α := eq.refl a

namespace eq
  @[inline] def rfl {α : Type u} {a : α} : a = a :> α :=
  eq.refl a

  @[hott, trans] def trans {α : Type u} {a b c : α}
    (p : a = b :> α) (q : b = c :> α) : a = c :> α :=
  begin induction p, assumption end

  @[hott, symm] def symm {α : Type u} {a b : α} (p : a = b :> α) :
    b = a :> α :=
  begin induction p, reflexivity end

  abbreviation inv {α : Type u} {a b : α} (p : a = b :> α) := symm p

  infixr ` ⬝ ` := trans
  postfix ⁻¹ := symm

  @[hott] def comp_inv {α : Type u} {a b : α} (p : a = b :> α) :
    p ⬝ p⁻¹ = eq.refl a :> a = a :> α :=
  begin induction p, trivial end

  @[hott] def inv_comp {α : Type u} {a b : α} (p : a = b :> α) :
    p⁻¹ ⬝ p = eq.refl b :> b = b :> α :=
  begin induction p, trivial end

  @[hott] def refl_left {α : Type u} {a b : α} (p : a = b :> α) :
    eq.refl a ⬝ p = p :> a = b :> α :=
  begin induction p, trivial end

  @[hott] def refl_right {α : Type u} {a b : α} (p : a = b :> α) :
    p ⬝ eq.refl b = p :> a = b :> α :=
  begin induction p, trivial end

  @[hott] def refl_twice {α : Type u} {a b : α} (p : a = b :> α) :
    rfl ⬝ p ⬝ rfl = p :> a = b :> α :=
  begin induction p, trivial end

  @[hott] def explode_inv {α : Type u} {a b c : α}
    (p : a = b :> α) (q : b = c :> α) :
    (p ⬝ q)⁻¹ = q⁻¹ ⬝ p⁻¹ :> c = a :> α :=
  begin induction p, induction q, trivial end

  @[hott] def inv_inv {α : Type u} {a b : α}
    (p : a = b :> α) : (p⁻¹)⁻¹ = p :> a = b :> α :=
  begin induction p, trivial end

  @[hott] def assoc {α : Type u} {a b c d : α}
    (p : a = b :> α) (q : b = c :> α) (r : c = d :> α) :
    p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r :=
  begin induction p, trivial end

  @[hott] def mpr {α β : Type u} (p : α = β) : β → α :=
  begin induction p, intro x, exact x end

  @[hott] def map {α : Type u} {β : Type v} {a b : α}
    (f : α → β) (p : a = b :> α) : f a = f b :> β :=
  begin induction p, reflexivity end
  infix [parsing_only] ` # ` := map

  @[hott] def map_inv {α : Type u} {β : Type v} {a b : α}
    (f : α → β) (p : a = b :> α) : (f # p⁻¹) = (f # p)⁻¹ :=
  begin induction p, reflexivity end

  @[hott] def trans_cancel_left {α : Type u} {a b c : α}
    (r : a = b) (p q : b = c) : r ⬝ p = r ⬝ q → p = q :=
  begin intro μ, induction r, exact μ end

  @[hott] def trans_cancel_right {α : Type u} {a b c : α}
    (r : b = c) (p q : a = b) : p ⬝ r = q ⬝ r → p = q := begin
    intro μ, induction r,
    transitivity, { symmetry, apply refl_right },
    symmetry, transitivity, { symmetry, apply refl_right },
    exact μ⁻¹
  end

  section
    variables {α : Type u} {β : Type v} {a b : α}
              (f : α → β) (p : a = b :> α)

    abbreviation cong := map f p
    abbreviation ap := map f p
  end

  @[hott] def ap₂ {α : Type u} {β : Type v} {a b : α}
    {p q : a = b :> α} (f : α → β)
    (r : p = q :> a = b :> α) :
    f # p = f # q :> f a = f b :> β :=
  begin induction r, reflexivity end

  class dotted (space : Type u) :=
  (point : space)

  structure pointed :=
  (space : Type u) (point : space)

  def loop_space (X : pointed) : pointed :=
  ⟨X.point = X.point :> X.space, eq.refl X.point⟩

  def iterated_loop_space : pointed → ℕ → pointed
  | X 0 := X
  | X (n + 1) := iterated_loop_space (loop_space X) n

  def loop_pointed_space (α : Type u) [h : dotted α] :=
  iterated_loop_space ⟨α, dotted.point α⟩

  notation `Ω` `[` n `]` `, ` X := (iterated_loop_space X n).space
  notation `Θ` `[` n `]` `, ` X := (iterated_loop_space X n).point

  notation `Ω¹`:25 X := (loop_pointed_space X 1).space
end eq

namespace not
  notation `¬` a := a → (𝟎 : Type)
  notation a ` ≠ ` b := ¬(a = b :> _)

  def absurd {α : Type u} {β : Type v} (h : α) (g : ¬α) : β :=
  ground_zero.proto.empty.cases_on (λ _, β) (g h)
end not

namespace whiskering
  variables {α : Type u} {a b c : α}
  variables {p q : a = b :> α} {r s : b = c :> α}
  variables {ν : p = q} {κ : r = s}

  @[hott] def right_whs (ν : p = q) (r : b = c) : p ⬝ r = q ⬝ r := begin
    induction r,
    exact (eq.refl_right p) ⬝ ν ⬝ (eq.refl_right q)⁻¹
  end
  infix ` ⬝ᵣ `:60 := right_whs

  @[hott] def left_whs (q : a = b) (κ : r = s) : q ⬝ r = q ⬝ s := begin
    induction q,
    exact (eq.refl_left r) ⬝ κ ⬝ (eq.refl_left s)⁻¹
  end
  infix ` ⬝ₗ `:60 := left_whs

  @[hott] def horizontal_comp₁ (ν : p = q) (κ : r = s) :=
  (ν ⬝ᵣ r) ⬝ (q ⬝ₗ κ)
  infix ` ⋆ `:65 := horizontal_comp₁

  @[hott] def horizontal_comp₂ (ν : p = q) (κ : r = s) :=
  (p ⬝ₗ κ) ⬝ (ν ⬝ᵣ s)
  infix ` ⋆′ `:65 := horizontal_comp₂

  @[hott] lemma comp_uniq : ν ⋆ κ = ν ⋆′ κ := begin
    induction p, induction r, induction ν, induction κ,
    reflexivity
  end

  @[hott] lemma loop₁ {α : Type u} {a : α}
    {ν κ : eq.refl a = eq.refl a} :
    ν ⬝ κ = ν ⋆ κ := begin
    symmetry, transitivity,
    { apply eq.map (⬝ eq.rfl ⬝ κ ⬝ eq.rfl),
      apply eq.refl_twice },
    apply eq.map (λ p, ν ⬝ p), apply eq.refl_twice
  end

  @[hott] lemma loop₂ {α : Type u} {a : α}
    {ν κ : eq.refl a = eq.refl a} :
    ν ⋆′ κ = κ ⬝ ν := begin
    transitivity,
    { apply eq.map (⬝ eq.rfl ⬝ ν ⬝ eq.rfl),
      apply eq.refl_twice },
    apply eq.map (λ p, κ ⬝ p), apply eq.refl_twice
  end

  @[hott] theorem «Eckmann–Hilton argument» {α : Type u} {a : α}
    (ν κ : eq.refl a = eq.refl a) : ν ⬝ κ = κ ⬝ ν :=
  loop₁ ⬝ comp_uniq ⬝ loop₂
end whiskering

end ground_zero.types