import ground_zero.HITs.interval ground_zero.types.sigma
open ground_zero ground_zero.HITs ground_zero.HITs.interval

hott theory

namespace ground_zero.theorems.fibration
  universes u v

  inductive leg {α : Sort u} : α → Type u
  | lam (f : I → α) : leg (f 0)

  inductive post {α : Sort u} : α → Type u
  | lam (f : I → α) : post (f 1)

  def lifting_property {α : Sort u} {β : Sort v} (p : α → β) :=
  Π {x : α}, leg (p x) → leg x

  def fibration (α : Sort u) (β : Sort v) :=
  Σ' (p : α → β), lifting_property p

  notation α ` ↠ ` β := fibration α β

  def lifting {α : Sort u} {β : α → Sort v} (f : I → α)
    (u : β (f 0)) : @leg (psigma β) ⟨f 0, u⟩ :=
  @leg.lam (psigma β) (λ i, ⟨f i,
    @interval.ind (β ∘ f) u (types.equiv.subst seg u)
      (types.equiv.path_over_subst types.eq.rfl) i⟩)

  def type_family {α : Sort u} (β : α → Sort v) :
    (Σ' x, β x) ↠ α := begin
    existsi psigma.fst, intros x f,
    cases x with x u, cases f with f u, apply lifting
  end

  def forward {α : Sort u} {β : α → Sort v} (x : α) :
    types.fib (@psigma.fst α β) x → β x
  | ⟨⟨y, u⟩, h⟩ := types.equiv.subst h u

  def backward {α : Sort u} {β : α → Sort v} (x : α) (u : β x) :
    types.fib (@psigma.fst α β) x :=
  ⟨⟨x, u⟩, by trivial⟩

  theorem fiber_over {α : Sort u} {β : α → Sort v} (x : α) :
    types.fib (@psigma.fst α β) x ≃ β x := begin
    existsi (forward x), split; existsi (@backward α β x),
    { intro u, cases u with u h, cases u with y u,
      induction h, fapply types.sigma.prod; trivial },
    { intro u, trivial }
  end
end ground_zero.theorems.fibration