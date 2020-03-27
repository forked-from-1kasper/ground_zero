import ground_zero.HITs.truncation
import ground_zero.types.sigma
open ground_zero.types ground_zero.HITs

namespace ground_zero.theorems.functions
universes u v

hott theory

@[hott] def fib_inh {α : Type u} {β : Type v} (f : α → β) :=
λ b, ∥fib f b∥

@[hott] def surj {α : Type u} {β : Type v} (f : α → β) :=
fiberwise (fib_inh f)

@[hott] def Im {α : Type u} {β : Type v} (f : α → β) :=
total (fib_inh f)

@[hott] def Im.incl {α : Type u} {β : Type v}
  {f : α → β} (h : surj f) : β → Im f :=
λ x, ⟨x, h x⟩

@[hott] def surj_impl_Im_eqv {α : Type u} {β : Type v}
  (f : α → β) (h : surj f) : Im f ≃ β := begin
  existsi sigma.fst, split; existsi Im.incl h,
  { intro x, induction x with x g,
    fapply sigma.prod, refl,
    apply truncation.uniq },
  { intro x, refl }
end

@[hott] def embedding {α : Type u} {β : Type v} (f : α → β) :=
Π (x y : α), @equiv.biinv (x = y) (f x = f y) (eq.map f)

@[hott] def is_connected (α : Type u) :=
Σ (x : α), Π y, ∥x = y∥

end ground_zero.theorems.functions