import ground_zero.HITs.interval
open ground_zero ground_zero.types ground_zero.HITs ground_zero.HITs.interval
open ground_zero.structures (prop)

hott theory

namespace ground_zero.theorems.fibration
  universes u v

  @[hott] def forward {α : Type u} {β : α → Type v} (x : α) :
    types.fib (@sigma.fst α β) x → β x :=
  λ ⟨⟨y, u⟩, h⟩, types.equiv.subst h u

  @[hott] def left {α : Type u} {β : α → Type v} (x : α) (u : β x) :
    types.fib (@sigma.fst α β) x :=
  ⟨⟨x, u⟩, Id.refl⟩

  @[hott] theorem fiber_over {α : Type u} {β : α → Type v} (x : α) :
    types.fib (@sigma.fst α β) x ≃ β x :=
  begin
    existsi (forward x), split; existsi (@left α β x),
    { intro u, cases u with u h, cases u with y u,
      induction h, fapply types.sigma.prod; trivial },
    { intro u, trivial }
  end

  inductive leg {α : Type u} : α → Type u
  | lam (f : I → α) : leg (f 0)

  inductive post {α : Type u} : α → Type u
  | lam (f : I → α) : post (f 1)

  @[hott] def lifting_property {α : Type u} {β : Type v} (p : α → β) :=
  Π {x : α}, leg (p x) → leg x

  @[hott] def fibration (α : Type u) (β : Type v) :=
  Σ (p : α → β), lifting_property p

  notation α ` ↠ ` β := fibration α β

  @[hott] def lifting {α : Type u} {β : α → Type v} (f : I → α)
    (u : β (f 0)) : @leg (sigma β) ⟨f 0, u⟩ :=
  @leg.lam (sigma β) (λ i, ⟨f i, @interval.ind (β ∘ f) u (equiv.subst seg u) Id.refl i⟩)

  @[hott] def type_family {α : Type u} (β : α → Type v) : (Σ x, β x) ↠ α :=
  begin
    existsi sigma.fst, intros x f, induction x with x u,
    apply @leg.rec_on α (λ x f, Π (u : β x), @leg (Σ x, β x) ⟨x, u⟩) x f, apply lifting
  end
end ground_zero.theorems.fibration